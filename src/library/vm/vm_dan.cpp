/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include "library/vm/vm.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_string.h"

namespace lean {

/* You want to put any global intialization here, and include a call to this function
   in the init_module.cpp file as I have done.

   These functions are used to ensure that initialization is performed in the correct
   order and only once.

   For example memory that should be alive for the duration of the execution should be
   allocated and free'd in these functions.
*/

/* Many of these functions can just be marked as static and registered with the VM here,
   you may want to declare them in the header file if you need to use them else where in the
   system. */
static lean::vm_obj dan_hello() {
    return to_obj(std::string("hello"));
}

/* IO functions right now are a little strange, but you can add them like so. */
// static lean::vm_obj dan_hello_io(vm_obj const &)

void initialize_vm_dan() {
    DECLARE_VM_BUILTIN(name({"dan", "hello"}), dan_hello);
}

void finalize_vm_dan() {
}
}
