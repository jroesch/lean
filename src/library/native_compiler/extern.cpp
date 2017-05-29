/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <string>
#include "library/attribute_manager.h"

namespace lean {
bool has_extern_attribute(environment const & env, name const & d) {
    return has_attribute(env, "extern", d);
}

std::string library_name(environment const & env, name const & d) {
    auto attr = static_cast<key_value_attribute const &>(get_attribute(env, "extern"));
    auto data = attr.get(env, d);
    auto key = data->m_pairs.find(name{"library"});
    return *key;
}

std::string symbol_name(environment const & env, name const & d) {
    auto attr = static_cast<key_value_attribute const &>(get_attribute(env, "extern"));
    auto data = attr.get(env, d);
    auto key = data->m_pairs.find(name{"name"});
    return *key;
}

void initialize_extern_attribute() {
    register_system_attribute(key_value_attribute(
        "extern",
        "mark declaration to be replaced with an implementation external to Lean",
        [=](environment const & env, lean::io_state const &, name const & n, unsigned, bool) {
            auto attr = static_cast<key_value_attribute const &>(get_attribute(env, "extern"));
            auto data = attr.get(env, n);

            if (!data->m_pairs.contains("library")) {
                throw exception("extern attribute requires the user to set the `library` key");
            }

            if (!data->m_pairs.contains("name")) {
                throw exception("extern attribute requires the user to set the `name` key");
            }

            return env;
        }));
}

void finalize_extern_attribute() {
}
}
