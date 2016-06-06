    /*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <fstream>
#include <iostream>
#include <iomanip>
#include <utility>
#include "cpp_emitter.h"
#include "kernel/environment.h"

namespace lean {

void cpp_emitter::emit_headers() {
    *this->m_output_stream << "#include \"lean/library/vm.h\""
                           << std::endl
                           << std::endl;
}

void cpp_emitter::emit_unreachable() {
    *this->m_output_stream << "lean_unreachable()";
}

void cpp_emitter::emit_local(unsigned idx) {
    *this->m_output_stream << "_$local_" << idx;
}

void cpp_emitter::emit_sconstructor(unsigned idx) {
    *this->m_output_stream << "mk_vm_simple(" << idx << ")";
}

void cpp_emitter::emit_mpz(mpz n) {
    *this->m_output_stream << "mk_vm_simple(" << 1337 << ")";
}

}
