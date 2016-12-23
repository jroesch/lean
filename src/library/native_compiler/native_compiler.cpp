/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch and Leonardo de Moura
*/
#include <sys/types.h>
#include <sys/stat.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string>
#include <vector>
#include <cstdio>
#include "util/fresh_name.h"
#include "util/sstream.h"
#include "kernel/instantiate.h"
#include "library/constants.h"
#include "library/trace.h"
#include "library/annotation.h"
#include "library/vm/vm.h"
#include "library/vm/optimize.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_format.h"
#include "library/util.h"
#include "library/compiler/simp_inductive.h"
#include "library/compiler/erase_irrelevant.h"
#include "library/compiler/nat_value.h"
#include "library/compiler/preprocess.h"
#include "library/native_compiler/native_compiler.h"
#include "library/native_compiler/options.h"
#include "library/native_compiler/cpp_compiler.h"
#include "library/native_compiler/extern.h"
#include "library/compiler/vm_compiler.h"
#include "library/module.h"
#include "library/native_compiler/used_defs.h"
#include "library/tactic/tactic_state.h"
#include "library/tactic/elaborate.h"
#include "util/lean_path.h"
#include "util/path.h"
#include "util/path_var.h"
// #include "util/executable.h"

static lean::path * g_lean_install_path = nullptr;

namespace lean {

expr mk_local(name const & n) {
    return ::lean::mk_local(n, mk_neutral_expr());
}

// Helper functions for setting up the install path on boot-up.
void initialize_install_path() {
    // 8 is the size of the string bin/lean which we want to remove from
    // the installed version of Lean.
#if defined(LEAN_EMSCRIPTEN)
    g_lean_install_path = new std::string;
#else
    auto p = get_exe_location();
    g_lean_install_path = new path(std::string(p.substr(0, p.size() - 8)));
#endif
}

path get_install_path() {
    return *g_lean_install_path;
}

extern_fn mk_lean_extern(name n, unsigned arity) {
    return extern_fn(true, n, arity);
}

extern_fn mk_extern(name n, unsigned arity) {
    return extern_fn(false, n, arity);
}

vm_obj extern_fn::to_obj() {
    throw "a";
}

// Returns the path to the Lean library based on the standard search path,
// and provided options.
std::vector<path> native_include_paths() {
    std::vector<path> paths;
    auto conf = native::get_config();
    auto native_include_path_var = path_var(conf.m_native_include_path);

    for (auto path : native_include_path_var.m_paths) {
        paths.push_back(path);
    }

    // Finally look in the default path.
    paths.push_back(get_install_path().append("include/lean_ext"));

    return paths;
}

std::vector<path> native_library_paths() {
    std::vector<path> paths;

    auto conf = native::get_config();
    auto native_library_path_var = path_var(conf.m_native_library_path);

    for (auto path : native_library_path_var.m_paths) {
        paths.push_back(path);
    }

    paths.push_back(get_install_path().append("lib"));

    return paths;
}

// Constructs a compiler with the native configuation options applied.
cpp_compiler compiler_with_native_config(native_compiler_mode mode) {
    auto conf = native::get_config();
    cpp_compiler gpp(conf.m_native_cc);

    if (mode == native_compiler_mode::Executable) {
        gpp = mk_executable_compiler(conf.m_native_cc);
        // The executable has two linkage strategies unlike the module compiler
        // we want to sometime use static linking, and sometimes dynamic.
        if (conf.m_native_dynamic) {
            gpp.link(LEAN_STATIC_LIB);
        } else {
            gpp.link(LEAN_SHARED_LIB);
        }
    } else {
        gpp = mk_shared_compiler(conf.m_native_cc);
    }

    auto include_paths = native_include_paths();
    auto library_paths = native_library_paths();

    // Setup include paths
    for (auto path : include_paths) {
        gpp.include_path(path.to_string());
    }

    for (auto path : library_paths) {
        gpp.library_path(path.to_string());
    }

    // Have g++ emit debug information.
    if (conf.m_native_emit_dwarf) {
        gpp.debug(true);
    }

    std::string binary(conf.m_native_binary);

    if (binary.size()) {
        gpp.output(binary);
    }

    return gpp;
}

void add_shared_dependencies(cpp_compiler & compiler) {
    compiler.link("gmp")
            .link("pthread")
            .link("mpfr");
}

/* This function constructs a config value located in library/native/config.lean */
vm_obj mk_lean_native_config(native_compiler_mode mode) {
    auto native_conf = native::get_config();

    vm_obj dump_passes;
    if (native_conf.m_native_dump == std::string("")) {
        dump_passes = mk_vm_simple(0);
    } else {
        dump_passes = mk_vm_simple(1);
    }

    vm_obj compilation_mode;
    if (mode == native_compiler_mode::Module) {
        compilation_mode = mk_vm_simple(0);
    } else if (mode == native_compiler_mode::Executable) {
        compilation_mode = mk_vm_simple(1);
    } else {
        lean_unreachable();
    }

    return mk_vm_constructor(0, dump_passes, compilation_mode, mk_vm_simple(0));
}

lean::vm_obj to_lean_procs(buffer<procedure> & procs) {
    // let procs_list = [];
    vm_obj procs_list = mk_vm_simple(0);
    // procs_list = tuple :: procs_list
    for (auto & p : procs) {
        auto tuple = mk_vm_constructor(0, { to_obj(p.m_name), to_obj(p.m_code) });
        procs_list = mk_vm_constructor(1, { tuple, procs_list });
    }

    return procs_list;
}

lean::vm_obj to_lean_extern_fns(buffer<extern_fn> & extern_fns) {
    // let procs_list = [];
    vm_obj externs_list = mk_vm_simple(0);
    // procs_list = tuple :: procs_list
    for (auto & e : extern_fns) {
        auto inner_tuple = mk_vm_constructor(0, { to_obj(e.m_name), to_obj(e.m_arity) });
        auto tuple = mk_vm_constructor(0, { mk_vm_simple(e.m_in_lean_namespace), inner_tuple });
        externs_list = mk_vm_constructor(1, { tuple, externs_list });
    }

    return externs_list;
}

format invoke_native_compiler(
    environment const & env,
    buffer<extern_fn> & extern_fns,
    buffer<procedure> & procs,
    native_compiler_mode mode)
{
    std::cout << "at the top of the native compiler" << std::endl;
    auto list_of_procs = to_lean_procs(procs);
    auto list_of_extern_fns = to_lean_extern_fns(extern_fns);
    auto conf_obj = mk_lean_native_config(mode);

    options opts = get_global_ios().get_options();
    // env = vm_monitor_register(env, {"debugger", "monitor"});
    // lean_assert(has_monitor(env));
    vm_state S(env, opts);
    scope_vm_state scoped(S);

    // We want the outer most layer of the compiler to
    // run in the tactic monad so it has access to prover APIs
    // exposed by the tactic monad. Ideally a majority of the compiler
    // will be pure Lean and thus verifiable.
    local_context lctx;
    tactic_state s = mk_tactic_state_for(env, opts, lctx, mk_constant("true"));

    auto compiler_name = name({"native", "compile"});
    auto cc = mk_native_closure(env, compiler_name, {});

    std::cout << "calling the native compiler" << std::endl;
    // We can now just use the VM to evaluate the native compiler, this should
    // handle the case where `cc` is either bytecode or native code.
    vm_obj tactic_obj = S.invoke(
        cc,
        conf_obj,
        list_of_extern_fns,
        list_of_procs,
        to_obj(s));

    if (is_constructor(tactic_obj) && cidx(tactic_obj) == 0) {
        return to_format(cfield(tactic_obj , 0));
    } else if (auto except = is_tactic_exception(S, tactic_obj)) {
        auto msg = std::get<0>(*except);
        std::cout << msg << std::endl;
        throw "foo";
    } else {
        throw "blah";
    }
}

// Returns the path at which we will generate code, if
// unspecified by the user it is randomly generated.
std::string get_code_path() {
    std::string store_code = native::get_config().m_native_store_code;
    if (store_code.size() > 0) {
        return store_code;
    } else {
        return std::string(std::tmpnam(nullptr)) + ".cpp";
    }
}

environment load_native_compiler(environment const & env) {
    std::vector<module_name> imports;
    imports.push_back({{"tools", "native"}, optional<unsigned>()});
    std::cout << "trying to import tools.native" << std::endl;
    return import_modules(env, "", imports, mk_olean_loader());
}

void native_compile(environment const & env_without,
                    buffer<extern_fn> & extern_fns,
                    buffer<procedure> & procs,
                    native_compiler_mode mode) {
    // Ensure we have loaded tools.native.
    auto env = load_native_compiler(env_without);
    std::cout << "import succeded" << std::endl;
    auto output_path = get_code_path();
    std::fstream out(output_path, std::ios_base::out);

    auto fmt = invoke_native_compiler(env, extern_fns, procs, mode);
    std::cout << "about to print the output" << std::endl;
    out << fmt << "\n\n";
    std::cout << "done with output" << std::endl;

    // For now just close this, then exit.
    out.close();

    // Get a compiler with the config specified by native options, placed
    // in the correct mode.
    auto gpp = compiler_with_native_config(mode);

    // Add all the shared link dependencies.
    add_shared_dependencies(gpp);

    gpp.file(output_path).run();
}

void native_preprocess(environment const & env, declaration const & d, buffer<procedure> & procs) {
    // Run the normal preprocessing and optimizations.
    preprocess(env, d, procs);
}

bool is_internal_decl(declaration const & d) {
    auto n = d.get_name();
    return (n == name("_neutral_") ||
            n == name({"native_compiler", "return"}) ||
            is_internal_cnstr(mk_constant(n)) ||
            is_internal_cases(mk_constant(n)) ||
            is_internal_proj(mk_constant(n)));
}

optional<extern_fn> get_builtin(name const & n) {
    auto internal_name = get_vm_builtin_internal_name(n);
    if (internal_name) {
        switch (get_vm_builtin_kind(n)) {
            case vm_builtin_kind::VMFun: {
                return optional<extern_fn>();
            }
            case vm_builtin_kind::CFun: {
                auto arity = get_vm_builtin_arity(n);
                return optional<extern_fn>(
                    mk_lean_extern(internal_name, arity));
            }
            case vm_builtin_kind::Cases: {
                return optional<extern_fn>(
                    mk_lean_extern(internal_name, 2u));
            }
        }
        lean_unreachable();
    } else {
        return optional<extern_fn>();
    }
}

void populate_extern_fns(
    environment const & env,
    used_defs const & used,
    buffer<extern_fn> & extern_fns, bool is_library) {
    used.m_used_names.for_each([&] (name const & n) {
        if (auto builtin = get_builtin(n)) {
             // std::cout << "extern fn: " << n << std::endl;
             extern_fns.push_back(mk_lean_extern(n, builtin.value().m_arity));
        } else if (has_extern_attribute(env, n)) {
            extern_fns.push_back(mk_extern(n, 0));
        } else if (is_library) {
            extern_fns.push_back(mk_extern(n, 0));
        }
    });
}

// This function returns the set of declarations eligble for native compilation.
//
// This function has some assumptions baked in. Our current model of module based
// native compilation is to assume any declarations in the current environment
// which *are* currently represented by bytecode are eligible for compilation.
//
// This means in order to perserve seperate compilation of packages you must
// generate shared libraries from the deepest module outwards.
//
// We may need to revist this strategy in the future.
void decls_to_native_compile(environment const & env, buffer<declaration> & decls) {
    env.for_each_declaration([&] (declaration const & d) {
        auto decl_name = d.get_name();
        auto vdecl = get_vm_decl(env, d.get_name());
        if (is_prefix_of("list", decl_name) && vdecl && vdecl->is_bytecode()) {
            decls.push_back(d);
        }
    });
}

void native_compile_package(environment const & env, path root) {
    buffer<extern_fn> extern_fns;
    buffer<declaration> decls;
    buffer<procedure> all_procs;

    decls_to_native_compile(env, decls);

    for (auto decl : decls) {
        // std::cout << decl.get_name() << std::endl;
        buffer<procedure> procs;
        native_preprocess(env, decl, procs);
        all_procs.append(procs);
    }

    native_compile(env, extern_fns, all_procs, native_compiler_mode::Module);
}

void native_compile_binary(environment const & env, declaration const & d) {
    lean_trace(name("native_compile"),
        tout() << "main_fn: " << d.get_name() << "\n";);

    lean_trace(name("native_compiler"),
        tout() << "main_body: " << d.get_value() << "\n";);

    // Preprocess the main function.
    buffer<procedure> all_procs;
    buffer<procedure> main_procs;
    buffer<extern_fn> extern_fns;
    native_preprocess(env, d, main_procs);

    // Compute the live set of names, we attach a callback that will be
    // invoked for every declaration encountered.
    used_defs used_names(env, [&] (declaration const & d) {
        buffer<procedure> procs;
        if (is_internal_decl(d)) {
            return;
        } else if (auto p = get_builtin(d.get_name())) {
            return;
            // extern_fns.push_back(p.value());
        } else if (auto p =  get_vm_builtin_cases_idx(env, d.get_name())) {
            return;
        } else {
            native_preprocess(env, d, procs);
            for (auto pair : procs) {
                used_names.names_in_expr(pair.m_code);
                all_procs.push_back(pair);
            }
        }
    });

    // We then loop over the set of procs produced by preprocessing the
    // main function, we transitively collect all names.
    for (auto pair : main_procs) {
        all_procs.push_back(pair);
        used_names.names_in_preprocessed_body(pair.m_code);
    }

    populate_extern_fns(env, used_names, extern_fns, false);

    // Finally we assert that there are no unprocessed declarations.
    lean_assert(used_names.stack_is_empty());

    native_compile(env, extern_fns, all_procs, native_compiler_mode::Executable);
}

void initialize_native_compiler() {
    native::initialize_options();
    initialize_install_path();
    register_trace_class({"compiler", "native"});
    register_trace_class({"compiler", "native", "preprocess"});
    register_trace_class({"compiler", "native", "cpp_compiler"});
}

void finalize_native_compiler() {
    native::finalize_options();
    delete g_lean_install_path;
}
}
