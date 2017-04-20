prelude

import init.data.nat

import init.algebra.field init.algebra.ordered_ring
import init.data.nat.lemmas
import init.data.int
import init.algebra.numeric.lemmas
import init.algebra.numeric.util
import init.algebra.numeric.monad
import init.algebra.numeric.add
import init.algebra.numeric.mul
import init.algebra.numeric.div

namespace algebra

open tactic
open numeric.lemmas

meta def cast_int : int → tactic nat
| (int.of_nat n) := return n
| _ := fail "can not convert int to nat"

meta def normalize_nat_sub (norm_value a b : expr) : normalizer_m (expr × expr) := do
  a' ← normalize a,
  b' ← normalize b,
  a_int ← as_int a'.fst,
  b_int ← as_int b'.fst,
  if b_int < a_int
  then do
    sum ← to_expr ``(@add nat _ %%norm_value %%(b'.fst)),
    rprf ← normalize sum,
    final_prf ← to_expr ``(nat_sub_pos %%a %%b %%(a'.fst) %%(b'.fst) %%norm_value %%(a'.snd) %%(b'.snd) %%(rprf.snd)),
    return (norm_value, final_prf)
  else do
    final_prf ← to_expr ``(@nat_sub_zero %%a %%b %%(a'.fst) %%(b'.fst) %%(a'.snd) %%(b'.snd) (sorry)),
    return (norm_value, final_prf)

meta def normalize_sub (norm_value a b : expr) : normalizer_m (expr × expr) :=
do ty ← current_ty,
   if ty = ```(nat)
   then normalize_nat_sub norm_value a b
   else do
     sum ← to_expr ``(%%a + (- %%b)),
     (nval, prf) ← normalize sum,
     final_prf ← to_expr ``(@subst_into_subtr %%ty _ %%a %%b %%(nval) %%(prf)),
     return (norm_value, final_prf)

meta def normalize_neg (norm_value a : expr) : normalizer_m (expr × expr) :=
do (nval, prf) ← normalize a,
   if is_zero nval
   then do
     final_prf ← to_expr ``(numeric.lemmas.neg_zero %%a %%prf),
     return (nval, final_prf)
   else match norm_value with
   | ```(neg _) := do
     final_prf ← to_expr ``(neg_congr %%a %%nval %%prf),
     return (norm_value, final_prf)
   | _ := to_expr ``(neg_neg %%a) >>= fun prf, return (nval, prf)
   end

meta def numeric_normalize : expr → tactic (expr × expr) :=
fun e,
if false -- fix this
then mk_eq_refl e >>= fun prf, return $ (e, prf)
else
do -- trace "normalize",
   norm_int ← as_int e,
   ty ← infer_type e,
   norm_value ← expr_of_int ty norm_int,
   -- trace $ "norm_value :" ++ to_string norm_int,
   in_normalizer_m ⟨ numeric_normalize, ty ⟩ $
   match e with
   | ```(%%a + %%b) := normalize_add norm_value a b
   | ```(%%a - %%b) := normalize_sub norm_value a b
   | ```(%%a * %%b) := normalize_mul norm_value a b
   | ```(%%a / %%b) := normalize_div norm_value a b
   | ```(neg %%a) := normalize_neg norm_value a
   | ```(bit0 %%bits) := do
     (nval, prf) ← numeric_normalize bits,
     final_prf ← to_expr ``(bit0_congr %%bits %%nval %%prf),
     return (norm_value, final_prf)
   | ```(bit1 %%bits) := do
     (nval, prf) ← numeric_normalize bits,
     final_prf ← to_expr ``(bit1_congr %%bits %%nval %%prf),
     return (norm_value, final_prf)
   | e := mk_eq_refl e >>= fun prf, return $ (e, prf)
   end

end algebra
