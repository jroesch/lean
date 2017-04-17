prelude

import init.data.nat

import init.algebra.field init.algebra.ordered_ring
import init.data.nat.lemmas
import init.data.int

namespace algebra

open tactic

-- TODO: factor these out
-- lemmas from num norm

-- end lemmas

section lemmas

universe u
variable {α : Type u}

def add1 [has_add α] [has_one α] (a : α) : α :=
a + 1

local attribute [reducible] bit0 bit1 add1
local attribute [simp] right_distrib left_distrib

private meta def u : tactic unit :=
`[unfold bit0 bit1 add1]

private meta def usimp : tactic unit :=
u >> `[simp]

lemma subst_into_sum [has_add α] (l r tl tr t : α) (prl : l = tl) (prr : r = tr)
        (prt : tl + tr = t) : l + r = t :=
by rw [-prt, prr, prl]

lemma add_zero [add_monoid α] (a : α) : a + zero = a :=
by simp

lemma zero_add [add_monoid α] (a : α) : zero + a = a :=
by simp

lemma one_plus_one [has_one α] [has_add α] : 1 + 1 = (2 : α) :=
begin
  unfold bit0,
  simp,
end

lemma bit0_congr [has_add α] (bits bits' : α) : bits = bits' → bit0 bits = bit0 bits' :=
begin
    intros,
    rw a,
end

end lemmas

-- Utils
meta def as_int : expr → option int
| ```(zero) := some 0
| ```(one) := some 1
| ```(bit0 %%bits) :=
  do i' ← as_int bits,
     return $ 2 * i'
| ```(bit1 %%bits) :=
  do i' ← as_int bits,
     return $ 2 * i' + 1
| ```(%%a + %%b) :=
  do a' ← as_int a,
     b' ← as_int b,
     return $ a' + b'
| ```(%%a * %%b) :=
  do a' ← as_int a,
     b' ← as_int b,
     return $ a' * b'
| ```(%%a - %%b) :=
  do a' ← as_int a,
     b' ← as_int b,
     return $ a' - b'
| ```(%%a / %%b) := none
| _ := none

meta def expr_of_nat (ty : expr) : nat → tactic expr
| 0 := to_expr `(@zero %%ty _)
| 1 := to_expr `(@one %%ty _)
| n :=
  do r ← expr_of_nat (n / 2),
  if n % 2 = 0
  then to_expr `(@bit0 %%ty _ %%r)
  else to_expr `(@bit1 %%ty _ _ %%r)

meta def expr_of_int (ty : expr) : int → tactic expr
| (int.of_nat n) := expr_of_nat ty n
| (int.neg_succ_of_nat n) :=
expr_of_nat ty n >>= fun i, to_expr ``(- %%i)

meta def is_numeral (e : expr) : bool :=
(as_int e).is_some

meta def is_div : expr → bool
| ```(%%a / %%b) := tt
| _ := ff

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

set_option eqn_compiler.max_steps 10000

-- Bit view
meta inductive bit_view : Type| both_bit1 : expr → expr → bit_view
| both_bit0 : expr → expr → bit_view
| bit1_bit0 : expr → expr → bit_view
| bit0_bit1 : expr → expr → bit_view
-- bool tells us whether one is the first arg or not
| bit1_one : bool → expr → bit_view
| bit0_one : bool → expr → bit_view
| both_one : bit_view
| any_zero : bool → expr → bit_view

open bit_view

meta def view_bits : expr → expr → option bit_view
| ```(bit1 %%a) ```(bit1 %%b) := some $ both_bit1 a b
| ```(bit0 %%a) ```(bit0 %%b) := some $ both_bit0 a b
| ```(bit1 %%a) ```(bit0 %%b) := some $ bit1_bit0 a b
| ```(bit0 %%a) ```(bit1 %%b) := some $ bit0_bit1 a b
| ```(bit1 %%a) ```(one) := some $ bit1_one tt a
| ```(one) ```(bit1 %%a) := some $ bit1_one ff a
| ```(bit0 %%a) ```(one) := some $ bit0_one tt a
| ```(one) ```(bit0 %%a) := some $ bit0_one ff a
| ```(one) ```(one) := some $ both_one
| ```(zero) a := some $ any_zero tt a
| a ```(zero) := some $ any_zero ff a
| _ _ := none

meta def normalize_add (norm_value : expr) : expr → expr → normalizer_m (expr × expr) :=
fun lhs rhs,
match view_bits lhs rhs with
| none := fail "...."
| some bv :=
match bv with
| both_bit1 a b := fail "bit1 bit1"
| both_bit0 a b := fail "bit0 bit0"
| bit1_bit0 a b := fail "bit1 bit0"
| bit0_bit1 a b := fail "bit0 bit1"
| bit1_one tt a := fail "one bit1"
| bit1_one ff a := fail "bit1 one"
| bit0_one tt a := fail "one bit0"
| bit0_one ff a := fail "bit0 one"
| both_one :=
do prf ← to_expr ``(one_plus_one),
   return (norm_value, prf)
| any_zero tt a :=
do prf ← to_expr ``(zero_add %%a),
   return (norm_value, prf)
| any_zero ff a :=
do prf ← to_expr ``(add_zero %%a),
   return (norm_value, prf)
end
end

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
   match e with
   | ```(%%a + %%b) := do
     lhs ← numeric_normalize a,
     rhs ← numeric_normalize b,
     in_normalizer_m ⟨ numeric_normalize, ty ⟩ $ do
       (_, prf) ← normalize_add_cases norm_value lhs.fst rhs.fst,
       final_prf ← to_expr ``(@subst_into_sum %%ty _ %%a %%b %%(lhs.fst) %%(rhs.fst) %%norm_value %%(lhs.snd) %%(rhs.snd) %%prf),
       return (norm_value, final_prf)
   | ```(%%a - %%b) :=
     do ty ← infer_type a,
        in_normalizer_m ⟨ numeric_normalize, ty ⟩ $ fail "sub"
   | ```(%%a * %%b) := fail "mul"
   | ```(%%a / %%b) := fail "div"
   | ```(bit0 %%bits) := do
     (nval, prf) ← numeric_normalize bits,
     final_prf ← to_expr ``(bit0_congr %%bits %%nval %%prf),
     return (norm_value, final_prf)
   | ```(bit1 %%bits) := fail "bit1"
   | e := mk_eq_refl e >>= fun prf, return $ (e, prf)
   end
end

end algebra
