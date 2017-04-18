prelude

import init.data.nat

import init.algebra.field init.algebra.ordered_ring
import init.data.nat.lemmas
import init.data.int
import init.algebra.numeric.lemmas
import init.algebra.numeric.util
import init.algebra.numeric.monad
import init.algebra.numeric.add

namespace algebra

open tactic
open numeric.lemmas

meta def normalize_nat_sub (norm_value a b : expr) : normalizer_m (expr × expr) := do
  a' ← normalize a,
  b' ← normalize b,
  let ints := (do ai ← as_int a'.fst, bi ← as_int b'.fst, return (ai, bi)),
  match ints with
  | some (a_int, b_int) := do
    if b_int < a_int
    then do
      sum ← to_expr ``(%%(a'.fst) + %%(b'.fst)),
      rprf ← normalize sum,
      final_prf ← to_expr ``(@nat_sub_pos %%a %%b %%(a'.fst) %%(b'.fst) %%norm_value %%(a'.snd) %%(b'.snd) %%(rprf.snd)),
      return (norm_value, final_prf)
    else do
      final_prf ← to_expr ``(@nat_sub_zero %%a %%b %%(a'.fst) %%(b'.fst) %%(a'.snd) %%(b'.snd) sorry),
      return (norm_value, final_prf)
  | none := tactic.fail "args aren't nats"
  end

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
   | _ := fail "neg neg" -- to_expr ``(neg_neg) >>= fun prf, return (nval, prf)
   end

meta def numeric_normalize : expr → tactic (expr × expr) :=
fun e,
if false -- fix this
then mk_eq_refl e >>= fun prf, return $ (e, prf)
else
let opt_norm_value := as_int e
in match opt_norm_value with
| none := fail $ "unable to normalize the expression: " ++ to_string e
| some norm_int :=
do ty ← infer_type e,
   norm_value ← expr_of_int ty norm_int,
   in_normalizer_m ⟨ numeric_normalize, ty ⟩ $
   match e with
   | ```(%%a + %%b) := normalize_add norm_value a b
   | ```(%%a - %%b) := normalize_sub norm_value a b
   | ```(%%a * %%b) := fail "mul"
   | ```(%%a / %%b) := fail "div"
   | ```(- %%a) := normalize_neg norm_value a
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
end

end algebra
