prelude

import init.data.nat
import init.algebra.field init.algebra.ordered_ring
import init.data.nat.lemmas
import init.data.int

open tactic

inductive rational
| frac : int → int → rational
| integer : int → rational

section

open rational

def rational.add : rational → rational → rational
| (frac i j) (frac a b) := frac (i * a + j * b) (a * b)
| (frac i j) (integer x) := frac (i + x * j) j
| (integer x) (frac i j) := frac (i + x * j) j
| (integer x) (integer y) := integer $ x + y

instance rat_has_add : has_add rational :=
⟨ rational.add ⟩

def rational.sub : rational → rational → rational
| (frac i j) (frac a b) := frac (i * a - j * b) (a * b)
| (frac i j) (integer x) := frac (i - x * j) j
| (integer x) (frac i j) := frac (x * j - i) j
| (integer x) (integer y) := integer $ x - y

instance rat_has_sub : has_sub rational :=
⟨ rational.sub ⟩

def rational.mul : rational → rational → rational
| (frac i j) (frac a b) := frac (i * a) (j * b)
| (frac i j) (integer x) := frac (i * x) j
| (integer x) (frac i j) := frac (x * i) j
| (integer x) (integer y) := integer $ x * y

instance rat_has_mul : has_mul rational :=
⟨ rational.mul ⟩

def rational.div : rational → rational → rational
| (frac i j) (frac a b) := (frac i j) * (frac b a)
| (frac i j) (integer x) := (frac i j) * (frac 1 x)
| (integer x) (frac i j) := (integer x) * (frac j i)
| (integer x) (integer y) := frac x y

instance rat_has_div : has_div rational :=
⟨ rational.div ⟩

end

meta def as_int : expr → tactic int
| ```(zero) := return 0
| ```(one) := return 1
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
     ty ← infer_type a,
     if ty = ```(nat)
     then return $ if b' < a' then (a' - b') else 0
     else return $ a' - b'
| ```(%%a / %%b) :=
  do a' ← as_int a,
     b' ← as_int b,
     ty ← infer_type a,
     if ty = ```(nat)
     then fail "nat div is not supported"
     else return $ a' / b'

| ```(neg %%a) := neg <$> as_int a
| _ := fail "unknown case in as_int"

meta def expr_of_nat (ty : expr) : nat → tactic expr
| 0 := to_expr ``(@zero %%ty _)
| 1 := to_expr ``(@one %%ty _)
| n :=
  do r ← expr_of_nat (n / 2),
  if n % 2 = 0
  then to_expr ``(@bit0 %%ty _ %%r)
  else to_expr ``(@bit1 %%ty _ _ %%r)

meta def expr_of_int (ty : expr) : int → tactic expr
| (int.of_nat n) := expr_of_nat ty n
| (int.neg_succ_of_nat n) :=
if ty = ```(nat)
then to_expr ``(zero)
else expr_of_nat ty (nat.succ n) >>= fun i, to_expr ``(- %%i)

meta def is_numeral (e : expr) : tactic bool :=
(as_int e >> return tt) <|> return ff

meta def is_div : expr → bool
| ```(%%a / %%b) := tt
| _ := ff

meta def is_neg : expr → bool
| ```(- %%a) := tt
| _ := ff

meta def is_zero : expr → bool
| ```(zero) := tt
| _ := ff

/-- A view on the bits of the operands, pattern matching many times directly on expression is
    expensive in the elaborator so we instead match once and provide a view on the binary
    representation of numbers.
-/
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

set_option eqn_compiler.max_steps 10000

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
