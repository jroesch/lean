/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <string>
#include <iostream>
#include "library/io_state.h"
#include "library/tactic/tactic_state.h"
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_llvm.h"

#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/FileSystem.h"
#include <algorithm>
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <memory>
#include <string>
#include <fstream>
#include <vector>

namespace lean {

llvm::LLVMContext * g_llvm_context = nullptr;

struct vm_llvm_context : public vm_external {
    llvm::LLVMContext * m_val;
    vm_llvm_context(llvm::LLVMContext * v):m_val(v) {}
    virtual ~vm_llvm_context() {}
    virtual void dealloc() override { this->~vm_llvm_context(); get_vm_allocator().deallocate(sizeof(vm_llvm_context), this); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_llvm_context(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_llvm_context))) vm_llvm_context(m_val); }
};

vm_obj to_obj(llvm::LLVMContext * ctxt) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_llvm_context))) vm_llvm_context(ctxt));
}

vm_obj global_context(vm_obj const &) {
    return to_obj(g_llvm_context);
}

// bool is_format(vm_obj const & o) {
//     return is_external(o) && dynamic_cast<vm_format*>(to_external(o));
// }

// format const & to_format(vm_obj const & o) {
//     lean_assert(is_external(o));
//     lean_assert(dynamic_cast<vm_format*>(to_external(o)));
//     return static_cast<vm_format*>(to_external(o))->m_val;
// }

// vm_obj to_obj(llvm::LLVMContext const & n) {
//     return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_format))) vm_format(n));
// }

// vm_obj put_nat(vm_obj const & n, vm_obj const &) {
//     if (is_simple(n))
//         get_global_ios().get_regular_stream() << cidx(n);
//     else
//         get_global_ios().get_regular_stream() << to_mpz(n);
//     return mk_vm_unit();
// }

// vm_obj get_line(vm_obj const &) {
//     if (get_global_ios().get_options().get_bool("server"))
//         throw exception("get_line: cannot read from stdin in server mode");
//     std::string str;
//     std::getline(std::cin, str);
//     return to_obj(str);
// }

// vm_obj forever (vm_obj const & action, vm_obj const &) {
//     while (true) {
//         invoke(action, mk_vm_simple(0));
//     }

//     return mk_vm_simple(0);
// }

struct vm_llvm_module : public vm_external {
    // Not sure the right way to store this, needs to stick around and be shared by all people with this handle,
    // totally mutable, non-functional object.
    std::shared_ptr<llvm::Module> m_val;

    vm_llvm_module(std::shared_ptr<llvm::Module> const & v) : m_val(v) {}

    virtual ~vm_llvm_module() {}
    virtual void dealloc() override { this->~vm_llvm_module(); get_vm_allocator().deallocate(sizeof(vm_llvm_module), this); }

    virtual vm_external * ts_clone(vm_clone_fn const &) override {
        lean_unreachable();
    }

    virtual vm_external * clone(vm_clone_fn const &) override {
        lean_unreachable();
    }
};

vm_obj to_obj(std::shared_ptr<llvm::Module> const & v) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_llvm_module))) vm_llvm_module(v));
}

std::shared_ptr<llvm::Module> to_module(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_llvm_module*>(to_external(o)));
    return static_cast<vm_llvm_module*>(to_external(o))->m_val;
}

vm_obj llvm_module_new(vm_obj const & module_name, vm_obj const &) {
    auto shared = std::make_shared<llvm::Module>(to_string(module_name).c_str(), *g_llvm_context);
    return to_obj(shared);
}

vm_obj llvm_print_module(vm_obj const & path_obj, vm_obj const & mod_obj, vm_obj const &) {
    auto path = to_string(path_obj);
    auto module = to_module(mod_obj);

    std::error_code error_code;
    llvm::raw_fd_ostream os(path, error_code, llvm::sys::fs::OpenFlags::F_RW);
    module->print(os, nullptr);

    return mk_vm_unit();
}

void initialize_vm_llvm() {
    g_llvm_context = new llvm::LLVMContext();
    DECLARE_VM_BUILTIN(name({"llvm", "global_context"}), global_context);
    DECLARE_VM_BUILTIN(name({"llvm", "module", "new"}), llvm_module_new);
    DECLARE_VM_BUILTIN(name({"llvm", "module", "write_to"}), llvm_print_module);
}

void finalize_vm_llvm() {
    delete g_llvm_context;
}
}
