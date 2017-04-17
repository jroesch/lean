prelude

import init.data.nat

import init.algebra.field init.algebra.ordered_ring
import init.data.nat.lemmas
import init.data.int
import init.algebra.numeric.lemmas
import init.algebra.numeric.util

namespace algebra

open tactic
open numeric.lemmas

-- Normalizer Monad
meta structure normalizer_state : Type :=
-- A function for normalizing recursively.
(normalizer : expr → tactic (expr × expr))
-- The type of the expression under normalization.
(current_ty : expr)

@[reducible] meta def normalizer_m := state_t normalizer_state tactic

meta def in_normalizer_m {A : Type} (st : normalizer_state) (action : normalizer_m A) : tactic A :=
prod.fst <$> action st

meta instance {α : Type} : has_coe (tactic α) (normalizer_m α) :=
⟨ fun t, fun s, do t' ← t, return (t', s) ⟩

meta def normalize (e : expr) : normalizer_m (expr × expr) :=
do st ← state_t.read,
   st.normalizer e

meta def current_ty : normalizer_m expr :=
do st ← state_t.read,
   return $ st.current_ty

open bit_view

meta def normalize_add (norm_value : expr) : expr → expr → normalizer_m (expr × expr) :=
fun lhs rhs,
match view_bits lhs rhs with
| none := fail "...."
| some bv :=
match bv with
| both_bit1 a b :=
  do sum ← to_expr `(%%a + %%b),
     (nval, prf) ← normalize sum,
     final_prf ← to_expr ``(bit1_add_bit1 %%a %%b %%nval %%prf),
     return (norm_value, final_prf)
| both_bit0 a b :=
  do sum ← to_expr `(%%a + %%b),
     (nval, prf) ← normalize sum,
     final_prf ← to_expr ``(bit0_add_bit0 %%a %%b %%nval %%prf),
     return (norm_value, final_prf)
| bit1_bit0 a b :=
  do sum ← to_expr `(%%a + %%b),
     (nval, prf) ← normalize sum,
     final_prf ← to_expr ``(bit1_add_bit0 %%a %%b %%nval %%prf),
     return (norm_value, final_prf)
| bit0_bit1 a b :=
  do sum ← to_expr `(%%a + %%b),
     (nval, prf) ← normalize sum,
     final_prf ← to_expr ``(bit0_add_bit1 %%a %%b %%nval %%prf),
     return (norm_value, final_prf)
| bit1_one tt a :=
  do add1 ← to_expr `(%%a + 1),
     (nval, prf) ← normalize add1,
     final_prf ← to_expr ``(bit1_add_one %%a %%nval %%prf),
     return (norm_value, final_prf)
| bit1_one ff a :=
  do add1 ← to_expr `(%%a + 1),
     (nval, prf) ← normalize add1,
     final_prf ← to_expr ``(one_add_bit1 %%a %%nval %%prf),
     return (norm_value, final_prf)
| bit0_one tt a :=
  do (nval, prf) ← normalize a,
     final_prf ← to_expr ``(bit0_add_one %%a %%nval %%prf),
     return (norm_value, final_prf)
| bit0_one ff a :=
  do (nval, prf) ← normalize a,
     final_prf ← to_expr ``(one_add_bit0 %%a %%nval %%prf),
     return (norm_value, final_prf)
| both_one :=
do prf ← to_expr ``(one_plus_one),
   return (norm_value, prf)
| any_zero tt a :=
do prf ← to_expr ``(numeric.lemmas.zero_add %%a),
   return (norm_value, prf)
| any_zero ff a :=
do prf ← to_expr ``(numeric.lemmas.add_zero %%a),
   return (norm_value, prf)
end
end

set_option eqn_compiler.max_steps 10000

meta def normalize_add_cases (norm_value : expr) : expr → expr → normalizer_m (expr × expr)
| ```(neg %%a) ```(neg %%b) := fail "neg neg"
| ```(neg %%a) b := fail "neg pos"
| a ```(neg %%b) := fail "pos neg"
| lhs rhs :=
if is_div lhs
then fail "div left"
else if is_div rhs
then fail "div right"
else normalize_add norm_value lhs rhs

set_option eqn_compiler.max_steps 2048

meta def normalize_sub (norm_value a b : expr) : normalizer_m (expr × expr) :=
do ty ← current_ty,
   if ty = ```(nat)
   then fail "nat sub"
   else do
     sum ← to_expr ``(%%a + (- %%b)),
     (nval, prf) ← normalize sum,
     final_prf ← to_expr ``(@subst_into_subtr %%ty _ %%a %%b %%(nval) %%(prf)),
     return (norm_value, final_prf)

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
   | ```(%%a + %%b) := do
     lhs ← normalize a,
     rhs ← normalize b,
     in_normalizer_m ⟨ numeric_normalize, ty ⟩ $ do
       (_, prf) ← normalize_add_cases norm_value lhs.fst rhs.fst,
       final_prf ← to_expr ``(@subst_into_sum %%ty _ %%a %%b %%(lhs.fst) %%(rhs.fst) %%norm_value %%(lhs.snd) %%(rhs.snd) %%prf),
       return (norm_value, final_prf)
   | ```(%%a - %%b) := normalize_sub norm_value a b
   | ```(%%a * %%b) := fail "mul"
   | ```(%%a / %%b) := fail "div"
   | ```(- %%a) := fail "neg"
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
