prelude

import init.data.nat

import init.algebra.field init.algebra.ordered_ring
import init.data.nat.lemmas
import init.data.int
import init.algebra.numeric.lemmas
import init.algebra.numeric.util
import init.algebra.numeric.monad

namespace algebra

open tactic
open numeric.lemmas
open bit_view

meta def normalize_mul_bits (norm_value : expr) : expr → expr → normalizer_m (expr × expr) :=
fun lhs rhs,
match view_bits lhs rhs with
| none := fail "...."
| some bv :=
match bv with
| both_bit1 a b := fail "bit1 bit1"
--   do sum ← to_expr ``(%%a + %%b + 1),
--      (nval, prf) ← normalize sum,
--      final_prf ← to_expr ``(bit1_add_bit1 %%a %%b %%nval %%prf),
--      return (norm_value, final_prf)
| both_bit0 a b := fail "bit0 bit0"
--   do sum ← to_expr ``(%%a + %%b),
--      (nval, prf) ← normalize sum,
--      final_prf ← to_expr ``(bit0_add_bit0 %%a %%b %%nval %%prf),
--      return (norm_value, final_prf)
| bit1_bit0 a b := fail "bit1 bit0"
--   do sum ← to_expr ``(%%a + %%b),
--      (nval, prf) ← normalize sum,
--      final_prf ← to_expr ``(bit1_add_bit0 %%a %%b %%nval %%prf),
--      return (norm_value, final_prf)
| bit0_bit1 a b := fail "bit0 bit1"
--   do sum ← to_expr ``(%%a + %%b),
--      (nval, prf) ← normalize sum,
--      final_prf ← to_expr ``(bit0_add_bit1 %%a %%b %%nval %%prf),
--      return (norm_value, final_prf)
| bit1_one tt a := fail "bit1 one"
--   do add1 ← to_expr ``(%%a + 1),
--      (nval, prf) ← normalize add1,
--      final_prf ← to_expr ``(bit1_add_one %%a %%nval %%prf),
--      return (norm_value, final_prf)
| bit1_one ff a := fail "one bit1"
--   do add1 ← to_expr ``(%%a + 1),
--      (nval, prf) ← normalize add1,
--      final_prf ← to_expr ``(one_add_bit1 %%a %%nval %%prf),
--      return (norm_value, final_prf)
| bit0_one tt a := fail "bit0 one"
--   do (nval, prf) ← normalize a,
--      final_prf ← to_expr ``(bit0_add_one %%a %%nval %%prf),
--      return (norm_value, final_prf)
| bit0_one ff a := fail "one bit0"
--   do (nval, prf) ← normalize a,
--      final_prf ← to_expr ``(one_add_bit0 %%a %%nval %%prf),
--      return (norm_value, final_prf)
| both_one := fail "one one"
-- do ty ← current_ty,
--    prf ← to_expr ``(@one_plus_one %%ty _ _),
--    return (norm_value, prf)
| any_zero tt a := fail "any zero"
-- do prf ← to_expr ``(numeric.lemmas.zero_add %%a),
--    return (norm_value, prf)
| any_zero ff a := fail "any zero"
-- do prf ← to_expr ``(numeric.lemmas.add_zero %%a),
--    return (norm_value, prf)
end
end

set_option eqn_compiler.max_steps 10000

meta def normalize_mul_cases (norm_value : expr) (lhs rhs : expr) : normalizer_m (expr × expr) :=
if is_div lhs
then fail "lhs div"
else if is_div rhs
then fail "rhs div"
else if is_zero lhs || is_zero rhs
then normalize_mul_bits norm_value lhs rhs
else if is_neg lhs
then (if is_neg rhs then fail "neg neg" else fail "neg pos")
else (if is_neg rhs then fail "pos neg" else fail "pos pos")

-- meta def normalize_mul_cases' (norm_value : expr): expr → expr → normalizer_m (expr × expr)
-- | ```(%%a / %%b) _ := fail "a"
-- | _ ```(%%a / %%b) := fail "b"
-- -- | ```(zero) ```(zero) := fail "zero"
-- -- | ```(neg %%a) ```(neg %%b) := fail "neg neg"
-- | _ _ := fail "foo"

-- set_option pp.max_depth 100000
-- set_option pp.max_steps 100000

-- #print normalize_mul_cases'

-- if is_div lhs
-- then fail "lhs div"
-- else if is_div rhs
-- then fail "rhs div"
-- else if is_zero lhs || is_zero rhs
-- then fail "zeros"
-- else if is_neg lhs
-- then (if is_neg rhs then fail "neg neg" else fail "neg pos")
-- else (if is_neg rhs then fail "pos neg" else fail "pos pos")
--   sum ← to_expr ``(%%a + %%b),
--   (nval, prf) ← normalize sum,
--   final_prf ← to_expr ``(neg_add_neg %%a %%b %%nval %%prf),
--   return (norm_value, final_prf)
-- | ```(neg %%a) b := do
--   sum ← to_expr ``(%%norm_value + %%a),
--   (nval, prf) ← normalize sum,
--   final_prf ← to_expr ``(neg_add_pos %%a %%nval %%norm_value %%prf),
--   return (norm_value, final_prf)
-- | a ```(neg %%b) := do
--   sum ← to_expr ``(%%norm_value + %%b),
--   (nval, prf) ← normalize sum,
--   final_prf ← to_expr ``(pos_add_neg %%nval %%b %%norm_value %%prf),
--   return (norm_value, final_prf)
-- | lhs rhs :=
-- if is_div lhs
-- then fail "div left"
-- else if is_div rhs
-- then fail "div right"
-- else normalize_add_bits norm_value lhs rhs

set_option eqn_compiler.max_steps 2048

meta def normalize_mul (norm_value a b : expr) : normalizer_m (expr × expr) :=
do lhs ← normalize a,
   rhs ← normalize b,
   ty ← current_ty,
   (nval, prf) ← normalize_mul_cases norm_value lhs.fst rhs.fst,
   final_prf ← to_expr ``(@subst_into_sum %%ty _ %%a %%b %%(lhs.fst) %%(rhs.fst) %%norm_value %%(lhs.snd) %%(rhs.snd) %%prf),
   return (norm_value, final_prf)

end algebra
