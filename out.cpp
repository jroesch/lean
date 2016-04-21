#include "lean_runtime.h"
#include "string.h"

static lean::obj string_empty = lean::mk_obj(0);

lean::obj prod_mk(lean::obj f0, lean::obj f1, lean::obj f2, lean::obj f3) {
return lean::mk_obj(0, { f0, f1, f2, f3 });
}

static lean::obj bool_tt = lean::mk_obj(1);

static lean::obj bool_ff = lean::mk_obj(0);

static lean::obj RealWorld_mk = lean::mk_obj(0);

lean::obj char_mk(lean::obj f0, lean::obj f1, lean::obj f2, lean::obj f3, lean::obj f4, lean::obj f5, lean::obj f6, lean::obj f7) {
return lean::mk_obj(0, { f0, f1, f2, f3, f4, f5, f6, f7 });
}

lean::obj string_str(lean::obj f0, lean::obj f1) {
return lean::mk_obj(1, { f0, f1 });
}

lean::obj ___lean__main();

lean::obj prod_rec_on(lean::obj __lean_nv_18_188, lean::obj __lean_nv_18_189);

lean::obj print_string(lean::obj __lean_nv_18_191);

lean::obj ___lean__main() {
lean::obj __lean_nv_18_164 = char_mk(bool_ff, bool_tt, bool_tt, bool_ff, bool_tt, bool_ff, bool_ff, bool_ff);
lean::obj __lean_nv_18_166 = char_mk(bool_ff, bool_tt, bool_tt, bool_ff, bool_ff, bool_tt, bool_ff, bool_tt);
lean::obj __lean_nv_18_168 = char_mk(bool_ff, bool_tt, bool_tt, bool_ff, bool_tt, bool_tt, bool_ff, bool_ff);
lean::obj __lean_nv_18_170 = char_mk(bool_ff, bool_tt, bool_tt, bool_ff, bool_tt, bool_tt, bool_ff, bool_ff);
lean::obj __lean_nv_18_172 = char_mk(bool_ff, bool_tt, bool_tt, bool_ff, bool_tt, bool_tt, bool_tt, bool_tt);
lean::obj __lean_nv_18_174 = char_mk(bool_ff, bool_ff, bool_tt, bool_ff, bool_ff, bool_ff, bool_ff, bool_ff);
lean::obj __lean_nv_18_176 = char_mk(bool_ff, bool_tt, bool_tt, bool_tt, bool_ff, bool_tt, bool_tt, bool_tt);
lean::obj __lean_nv_18_178 = char_mk(bool_ff, bool_tt, bool_tt, bool_ff, bool_tt, bool_tt, bool_tt, bool_tt);
lean::obj __lean_nv_18_180 = char_mk(bool_ff, bool_tt, bool_tt, bool_tt, bool_ff, bool_ff, bool_tt, bool_ff);
lean::obj __lean_nv_18_182 = char_mk(bool_ff, bool_tt, bool_tt, bool_ff, bool_tt, bool_tt, bool_ff, bool_ff);
lean::obj __lean_nv_18_184 = char_mk(bool_ff, bool_tt, bool_tt, bool_ff, bool_ff, bool_tt, bool_ff, bool_ff);
lean::obj __lean_nv_18_183 = string_str(__lean_nv_18_184, string_empty);
lean::obj __lean_nv_18_181 = string_str(__lean_nv_18_182, __lean_nv_18_183);
lean::obj __lean_nv_18_179 = string_str(__lean_nv_18_180, __lean_nv_18_181);
lean::obj __lean_nv_18_177 = string_str(__lean_nv_18_178, __lean_nv_18_179);
lean::obj __lean_nv_18_175 = string_str(__lean_nv_18_176, __lean_nv_18_177);
lean::obj __lean_nv_18_173 = string_str(__lean_nv_18_174, __lean_nv_18_175);
lean::obj __lean_nv_18_171 = string_str(__lean_nv_18_172, __lean_nv_18_173);
lean::obj __lean_nv_18_169 = string_str(__lean_nv_18_170, __lean_nv_18_171);
lean::obj __lean_nv_18_167 = string_str(__lean_nv_18_168, __lean_nv_18_169);
lean::obj __lean_nv_18_165 = string_str(__lean_nv_18_166, __lean_nv_18_167);
lean::obj __lean_nv_18_163 = string_str(__lean_nv_18_164, __lean_nv_18_165);
return print_string(__lean_nv_18_163);
}

lean::obj prod_rec_on(lean::obj __lean_nv_18_188, lean::obj __lean_nv_18_189) {
lean::obj __lean_nv_18_190 = __lean_nv_18_188;
switch (__lean_nv_18_190.cidx()) {
    case 0: {
        return __lean_nv_18_189.apply(__lean_nv_18_190[2], __lean_nv_18_190[3]);
    }
    default:
        throw "error";
}
}

lean::obj print_string(lean::obj __lean_nv_18_191) {
    lean::obj __lean_nv_18_193 = string_to_raw_string(RealWorld_mk, __lean_nv_18_191);
    auto f = lean::mk_closure_core((void*)raw_print, 2, 0, nullptr);
    return prod_rec_on(__lean_nv_18_193, f);
}

int main() {
    lean::run_lean_main(___lean__main);
    return 0;
}
