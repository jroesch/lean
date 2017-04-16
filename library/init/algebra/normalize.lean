prelude

import init.data.nat

import init.algebra.field init.algebra.ordered_ring
import init.data.nat.lemmas
import init.data.int

namespace algebra

open tactic

meta def as_int : expr → option int
| ```(zero) := some 0
| ```(one) := some 1
| ```(bit0 %%bits) :=
  do i' ← as_int bits,
     return $ 2 * i'
| ```(bit1 %%bits) :=
  do i' ← as_int bits,
     return $ 2 * i' + 1
| _ := none

meta def is_numeral (e : expr) : bool :=
(as_int e).is_some

meta structure normalizer_state : Type :=
-- A function for normalizing recursively.
(normalizer : expr → tactic (expr → expr))
-- The type of the expression under normalization.
(current_ty : expr)

@[reducible] meta def normalizer_m := state_t normalizer_state tactic

meta def normalize_add : normalizer_m (expr × expr) :=
return (```(one), ```(one))

meta def numeric_normalize : expr → tactic (expr × expr)
| ```(%%a + %%b) := fail "add"
| ```(%%a - %%b) := fail "sub"
| ```(%%a * %%b) := fail "mul"
| ```(%%a / %%b) := fail "div"
| ```(bit0 %%bits) := fail "bit0"
| ```(bit1 %%bits) := fail "bit1"
| e := mk_eq_refl e >>= fun prf, return $ (e, prf)

end algebra
