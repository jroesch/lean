/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <iostream>
#include "library/io_state.h"
#include "library/tactic/tactic_state.h"
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"

namespace lean {
vm_obj mk_io_result(vm_obj const & r) {
    return mk_vm_pair(r, mk_vm_unit());
}

vm_obj put_str(vm_obj const & str, vm_obj const &) {
    get_global_ios().get_regular_stream() << to_string(str);
    return mk_io_result(mk_vm_unit());
}

vm_obj put_nat(vm_obj const & n, vm_obj const &) {
    if (is_simple(n))
        get_global_ios().get_regular_stream() << cidx(n);
    else
        get_global_ios().get_regular_stream() << to_mpz(n);
    return mk_io_result(mk_vm_unit());
}

vm_obj get_line(vm_obj const &) {
    if (get_global_ios().get_options().get_bool("server"))
        throw exception("get_line: cannot read from stdin in server mode");
    std::string str;
    std::getline(std::cin, str);
    return mk_io_result(to_obj(str));
}

/* A temporary, but not great file-IO solution. */
vm_obj write_file_core(vm_obj const & path_obj, vm_obj const & contents_obj, vm_obj const &) {
    auto path = to_string(path_obj);
    auto contents = to_string(contents_obj);
    std::fstream fs;
    fs.open(path, std::fstream::out);
    fs << contents;
    return mk_io_result(mk_vm_unit());
}

vm_obj forever(vm_obj const & action, vm_obj const &) {
    while (true) {
        invoke(action, mk_vm_simple(0));
    }
    return mk_io_result(mk_vm_simple(0));
}

void initialize_vm_io() {
    DECLARE_VM_BUILTIN("put_str", put_str);
    DECLARE_VM_BUILTIN("put_nat", put_nat);
    DECLARE_VM_BUILTIN("get_line", get_line);
    DECLARE_VM_BUILTIN("forever", forever);
    DECLARE_VM_BUILTIN("write_file_core", write_file_core);
}

void finalize_vm_io() {
}
}
