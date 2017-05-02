/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jared Roesch
*/
#if defined(LEAN_JSON)
#include <list>
#include <string>
#include <vector>
#include <algorithm>
#include <clocale>
#include "frontends/lean/module_parser.h"
#include "library/library_task_builder.h"
#include "util/lean_path.h"
#include "util/sexpr/option_declarations.h"
#include "util/timer.h"
#include "library/mt_task_queue.h"
#include "library/st_task_queue.h"
#include "library/attribute_manager.h"
#include "library/tactic/tactic_state.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/info_manager.h"
#include "frontends/lean/interactive.h"
#include "shell/interactive_process.h"

namespace lean {

struct all_messages_msg {
    std::vector<message> m_msgs;

    json to_json_response() const {
        auto msgs = json::array();
        for (auto & msg : m_msgs)
            msgs.push_back(json_of_message(msg));

        json j;
        j["response"] = "all_messages";
        j["msgs"] = msgs;
        return j;
    }
};

interactive::interactive(unsigned num_threads, search_path const & path, environment const & initial_env, io_state const & ios) :
        m_path(path), m_initial_env(initial_env), m_ios(ios) {
//     m_ios.set_regular_channel(std::make_shared<stderr_channel>());
//     m_ios.set_diagnostic_channel(std::make_shared<stderr_channel>());

//     m_msg_handler.reset(new message_handler(this, &m_lt, num_threads > 0));
//     m_tasks_handler.reset(new tasks_handler(this, &m_lt, num_threads > 0));

//     m_lt.add_listener([&] (std::vector<log_tree::event> const & evs) {
//         m_msg_handler->on_event(evs);
//         m_tasks_handler->on_event(evs);
//     });

//     scope_global_ios scoped_ios(m_ios);
// #if defined(LEAN_MULTI_THREAD)
//     if (num_threads == 0) {
//         m_tq.reset(new st_task_queue);
//     } else {
//         m_tq.reset(new mt_task_queue(num_threads));
//     }
// #else
//     m_tq.reset(new st_task_queue());
// #endif

//     set_task_queue(m_tq.get());
//     m_mod_mgr.reset(new module_mgr(this, m_lt.get_root(), m_path, m_initial_env, m_ios));
//     m_mod_mgr->set_use_snapshots(true);
//     m_mod_mgr->set_save_olean(false);
}

interactive::~interactive() {
    m_mod_mgr->cancel_all();
    cancel(m_bg_task_ctok);
    m_tq->evacuate();
}

struct interactive::cmd_req {
    unsigned m_seq_num = static_cast<unsigned>(-1);
    std::string m_cmd_name;
    json m_payload;
};

struct interactive::cmd_res {
    cmd_res() {}
    cmd_res(unsigned seq_num, json const & payload) : m_seq_num(seq_num), m_payload(payload) {}
    cmd_res(unsigned seq_num, std::string const & error_msg) : m_seq_num(seq_num), m_error_msg(error_msg) {}

    unsigned m_seq_num = static_cast<unsigned>(-1);
    json m_payload;
    optional<std::string> m_error_msg;

    json to_json_response() const {
        json j;
        if (m_error_msg) {
            j["response"] = "error";
            j["message"] = *m_error_msg;
        } else {
            j = m_payload;
            j["response"] = "ok";
        }
        j["seq_num"] = m_seq_num;
        return j;
    }
};

struct unrelated_error_msg {
    std::string m_msg;

    json to_json_response() const {
        json j;
        j["response"] = "error";
        j["message"] = m_msg;
        return j;
    }
};

// Debugging functions for use in GDB.
interactive * g_interactive = nullptr;
void interactive_dump_log_tree() {
    g_interactive->get_log_tree().print_to(std::cerr);
}

void interactive::run() {
    flet<interactive *> _(g_interactive, this);

    scope_global_ios scoped_ios(m_ios);

    /* Leo: we use std::setlocale to make sure decimal period is displayed as ".".
       We added this hack because the json library code used for ensuring this property
       was crashing when compiling Lean on Windows with mingw. */
#if !defined(LEAN_EMSCRIPTEN)
    std::setlocale(LC_NUMERIC, "C");
#endif

    while (true) {
        try {
            std::string req_string;
            std::getline(std::cin, req_string);
            if (std::cin.eof()) return;

            json req = json::parse(req_string);

            handle_request(req);
        } catch (std::exception & ex) {
            send_msg(unrelated_error_msg{ex.what()});
        }
    }
}

void interactive::handle_request(json const & jreq) {
    cmd_req req;
    req.m_seq_num = jreq.at("seq_num");
    try {
        req.m_cmd_name = jreq.at("command");
        req.m_payload = jreq;
        handle_request(req);
    } catch (std::exception & ex) {
        send_msg(cmd_res(req.m_seq_num, std::string(ex.what())));
    }
}

void interactive::handle_request(interactive::cmd_req const & req) {
    std::string command = req.m_cmd_name;

    if (command == "sync") {
        send_msg(handle_sync(req));
    } else if (command == "complete") {
        handle_complete(req);
    } else if (command == "sleep") {
        chrono::milliseconds small_delay(1000);
        this_thread::sleep_for(small_delay);
    } else if (command == "long_sleep") {
        chrono::milliseconds small_delay(10000);
        this_thread::sleep_for(small_delay);
    } else {
        send_msg(cmd_res(req.m_seq_num, std::string("unknown command")));
    }
}

interactive::cmd_res interactive::handle_sync(interactive::cmd_req const & req) {
    std::string new_file_name = req.m_payload.at("file_name");
    std::string new_content = req.m_payload.at("content");

    auto mtime = time(nullptr);

    bool needs_invalidation = true;

    auto & ef = m_open_files[new_file_name];
    if (ef.m_content != new_content) {
        ef.m_content = new_content;
        ef.m_mtime = mtime;
        needs_invalidation = true;
    } else {
        needs_invalidation = false;
    }

    json res;
    if (needs_invalidation) {
        m_mod_mgr->invalidate(new_file_name);
        res["message"] = "file invalidated";
    } else {
        res["message"] = "file unchanged";
    }

    return { req.m_seq_num, res };
}

// optional<module_parser_result> get_closest_snapshot(std::shared_ptr<module_info const> const & mod_info, pos_info p) {
//     auto res = mod_info->m_snapshots;

//     while (res && res->m_next) {
//         if (auto next = peek(res->m_next)) {
//             if (next->m_range.m_end < p) {
//                 res = next;
//             } else {
//                 break;
//             }
//         } else {
//             break;
//         }
//     }

//     return res;
// }

// void parse_breaking_at_pos(module_id const & mod_id, std::shared_ptr<module_info const> mod_info, pos_info pos,
//                            bool complete = false) {
//     if (auto snap = get_closest_snapshot(mod_info, pos)) {
//         // ignore messages from reparsing
//         log_tree null;
//         scope_log_tree scope_lt(null.get_root());
//         snap->m_lt = logtree();
//         snap->m_cancel = global_cancellation_token();

//         auto p = std::make_shared<module_parser>(mod_id, *mod_info->m_lean_contents, environment(), mk_dummy_loader());
//         p->save_info(false);
//         p->use_separate_tasks(false);
//         p->break_at_pos(pos, complete);

//         p->resume(*snap, {});
//     }
// }

json interactive::autocomplete(std::shared_ptr<module_info const> const & mod_info, bool skip_completions,
                          pos_info const & pos0) {
    // auto pos = pos0;
    // if (pos.second == 0)
    //     pos.first--;
    // pos.second--;
    // json j;

    // if (auto snap = get_closest_snapshot(mod_info, pos)) {
    //     try {
    //         parse_breaking_at_pos(mod_info->m_mod, mod_info, pos, true);
    //     } catch (break_at_pos_exception & e) {
    //         report_completions(snap->m_snapshot_at_end->m_env, snap->m_snapshot_at_end->m_options,
    //                            pos0, skip_completions, m_path, mod_info->m_mod.c_str(),
    //                            e, j);
    //     } catch (throwable & ex) {}
    // }
    // return j;
}

void interactive::handle_complete(cmd_req const & req) {
    cancel(m_bg_task_ctok);
    m_bg_task_ctok = mk_cancellation_token();

    std::string fn = req.m_payload.at("file_name");
    pos_info pos = {req.m_payload.at("line"), req.m_payload.at("column")};
    bool skip_completions = false;
    if (req.m_payload.count("skip_completions"))
        skip_completions = req.m_payload.at("skip_completions");

    auto mod_info = m_mod_mgr->get_module(fn);

    auto complete_gen_task =
        task_builder<json>([=] { return autocomplete(mod_info, skip_completions, pos); })
        .wrap(library_scopes(log_tree::node()))
        .set_cancellation_token(m_bg_task_ctok)
        .build();

    taskq().submit(task_builder<unit>([this, req, complete_gen_task] {
        try {
            send_msg(cmd_res(req.m_seq_num, get(complete_gen_task)));
        } catch (throwable & ex) {
            send_msg(cmd_res(req.m_seq_num, std::string(ex.what())));
        }
        return unit{};
    }).depends_on(complete_gen_task).build());
}

std::tuple<std::string, module_src, time_t> interactive::load_module(module_id const & id, bool can_use_olean) {
    if (m_open_files.count(id)) {
        auto & ef = m_open_files[id];
        return std::make_tuple(ef.m_content, module_src::LEAN, ef.m_mtime);
    }
    return m_fs_vfs.load_module(id, can_use_olean);
}

template <class Msg>
void interactive::send_msg(Msg const & m) {
    json j = m.to_json_response();
    unique_lock<mutex> _(m_out_mutex);
    std::cout << j << std::endl;
}

void initialize_interactive_process() {
}

void finalize_interactive_process() {
}

}
#endif

