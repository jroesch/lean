prelude

import init.data.nat
import init.algebra.field init.algebra.ordered_ring
import init.data.nat.lemmas
import init.data.int

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
