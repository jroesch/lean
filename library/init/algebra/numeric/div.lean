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

-- meta def normalize_mul_bits (norm_value : expr) : expr → expr → normalizer_m (expr × expr) :=
-- fun lhs rhs,
-- match view_bits lhs rhs with
-- | none := fail "...."
-- | some bv :=
-- match bv with
-- | both_bit1 a b :=
--   do mul ← to_expr ``(%%a * bit1 %%b),
--      (mval, mprf) ← normalize mul,
--      sum ← to_expr ``(bit0 %%mval + bit1 %%b),
--      (sval, sprf) ← normalize sum,
--      final_prf ← to_expr ``(bit1_mul_any %%a (bit1 %%b) %%mval %%sval %%mprf %%sprf),
--      return (norm_value, final_prf)
-- | both_bit0 a b :=
--   do mul ← to_expr ``(%%a * (bit0 %%b)),
--      (nval, prf) ← normalize mul,
--      final_prf ← to_expr ``(bit0_mul_any %%a (bit0 %%b) %%nval %%prf),
--      return (norm_value, final_prf)
-- | bit1_bit0 a b :=
--   do mul ← to_expr ``((bit1 %%a) * %%b),
--      (nval, prf) ← normalize mul,
--      final_prf ← to_expr ``(any_mul_bit0 (bit1 %%a) %%b %%nval %%prf),
--      return (norm_value, final_prf)
-- | bit0_bit1 a b :=
--    do mul ← to_expr ``(%%a * (bit1 %%b)),
--      (nval, prf) ← normalize mul,
--      final_prf ← to_expr ``(bit0_mul_any %%a (bit1 %%b) %%nval %%prf),
--      return (norm_value, final_prf)
-- | bit1_one tt a :=
--   do e ← to_expr ``(bit1 %%a),
--      (nval, prf) ← normalize e,
--      final_prf ← to_expr ``(any_mul_one (bit1 %%a) %%nval %%prf),
--      return (norm_value, final_prf)
-- | bit1_one ff a :=
--   do e ← to_expr ``(bit1 %%a),
--      (nval, prf) ← normalize e,
--      final_prf ← to_expr ``(one_mul_any (bit1 %%a) %%nval %%prf),
--      return (norm_value, final_prf)
-- | bit0_one tt a :=
--   do e ← to_expr ``(bit0 %%a),
--      (nval, prf) ← normalize e,
--      final_prf ← to_expr ``(any_mul_one (bit0 %%a) %%nval %%prf),
--      return (norm_value, final_prf)
-- | bit0_one ff a :=
--   do e ← to_expr ``(bit0 %%a),
--      (nval, prf) ← normalize e,
--      final_prf ← to_expr ``(one_mul_any (bit0 %%a) %%nval %%prf),
--      return (norm_value, final_prf)
-- | both_one :=
-- do ty ← current_ty,
--    prf ← to_expr ``(@one_mul_any %%ty _ one one (eq.refl one)),
--    return (norm_value, prf)
-- | any_zero tt a :=
--   do prf ← to_expr ``(numeric.lemmas.zero_mul %%a),
--      return (norm_value, prf)
-- | any_zero ff a :=
--    do prf ← to_expr ``(numeric.lemmas.mul_zero %%a),
--       return (norm_value, prf)
-- end
-- end

-- meta def prj_neg : expr → expr
-- | ```(neg %%n) := n
-- | e := e

meta def normalize_div_cases (norm_value : expr) (lhs rhs : expr) : normalizer_m (expr × expr) :=
fail "foo"

-- do -- trace "in mul cases",
-- if is_div lhs
-- then fail "lhs div"
-- else if is_div rhs
-- then fail "rhs div"
-- else if is_zero lhs || is_zero rhs
-- then normalize_mul_bits norm_value lhs rhs
-- else if is_neg lhs
-- then (if is_neg rhs
--       then do mul ← to_expr ``(%%(prj_neg lhs) * %%(prj_neg rhs)),
--               (nval, prf) ← normalize mul,
--               final_prf ← to_expr ``(numeric.lemmas.neg_mul_neg %%(prj_neg lhs) %%(prj_neg rhs) %%nval %%prf),
--               return (norm_value, final_prf)
--       else do mul ← to_expr ``(%%(prj_neg lhs) * %%rhs),
--               (nval, prf) ← normalize mul,
--               final_prf ← to_expr ``(numeric.lemmas.neg_mul_pos %%(prj_neg lhs) %%rhs %%nval %%prf),
--               return (norm_value, final_prf))
-- else (if is_neg rhs
--       then do mul ← to_expr ``(%%lhs * %%(prj_neg rhs)),
--               (nval, prf) ← normalize mul,
--               final_prf ← to_expr ``(numeric.lemmas.pos_mul_neg %%lhs %%(prj_neg rhs) %%nval %%prf),
--               return (norm_value, final_prf)
--       else normalize_mul_bits norm_value lhs rhs)

meta def normalize_div (norm_value a b : expr) : normalizer_m (expr × expr) :=
do -- trace "norm mult",
   lhs ← normalize a,
   rhs ← normalize b,
   ty ← current_ty,
   (nval, prf) ← normalize_div_cases norm_value lhs.fst rhs.fst,
   final_prf ← to_expr ``(@subst_into_prod %%ty _ %%a %%b %%(lhs.fst) %%(rhs.fst) %%norm_value %%(lhs.snd) %%(rhs.snd) %%prf),
   return (norm_value, final_prf)

end algebra
