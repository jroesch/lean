/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch, Robert Lewis and Leonardo de Moura
-/

prelude

import init.algebra.field init.algebra.ordered_ring
import init.data.nat.lemmas
import init.data.int

namespace numeric.normalizer
namespace lemmas

universe u
variable {α : Type u}

local attribute [reducible] bit0 bit1
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

lemma bit1_congr [has_add α] [has_one α] (bits bits' : α) : bits = bits' → bit1 bits = bit1 bits' :=
begin
    intros,
    rw a,
end

lemma neg_congr [has_neg α] (bits bits' : α) (h : bits = bits') : neg bits = neg bits' :=
by rw -h

lemma subst_into_subtr [add_group α] (l r t : α) (h : l + -r = t) : l - r = t :=
by simp [h]

lemma bit0_add_one [has_one α] [has_add α] (a a' : α) (h : a = a') : bit0 a + 1 = bit1 a' :=
begin
    rw h,
end

lemma one_add_bit0 [has_one α] [add_comm_semigroup α] (a a' : α) (h : a = a') : 1 + bit0 a = bit1 a' :=
begin
    unfold bit1,
    rewrite h,
    rewrite add_comm,
end

lemma bit1_add_one [has_one α] [add_comm_semigroup α] (a r : α) (h : a + 1 = r) : bit1 a + 1 = bit0 r :=
begin
unfold bit1 bit0,
rsimp,
end

lemma one_add_bit1 [has_one α] [add_comm_semigroup α] (a r : α) (h : a + 1 = r) : 1 + bit1 a = bit0 r :=
begin
    unfold bit1 bit0,
    rsimp,
end

lemma bit0_add_bit0 [add_comm_semigroup α] (a b r : α) (h : a + b = r) : bit0 a + bit0 b = bit0 r :=
begin
  unfold bit1 bit0,
  rw -h,
  simp,
end

lemma bit1_add_bit0 [add_comm_semigroup α] [has_one α] (a b r : α) (h : a + b = r) : bit1 a + bit0 b = bit1 r :=
begin
  unfold bit1 bit0,
  rw -h,
  simp,
end

lemma bit0_add_bit1 [add_comm_semigroup α] [has_one α] (a b r : α) (h : a + b = r) : bit0 a + bit1 b = bit1 r :=
begin
  unfold bit1 bit0,
  rw -h,
  simp,
end

lemma bit1_add_bit1 [add_comm_semigroup α] [has_one α] (a b r : α) (h : a + b + 1 = r) : bit1 a + bit1 b = bit0 r :=
begin
  unfold bit1 bit0,
  rw -h,
  simp,
end

lemma neg_neg_helper [add_group α] (a b : α) (h : a = -b) : -a = b :=
by simp [h]

lemma neg_add_neg [add_comm_group α] (a b c : α) (h : a + b = c) : -a + -b = -c :=
begin apply @neg_inj α, simp [neg_add, neg_neg], assumption end

lemma pos_add_neg [add_comm_group α] (a b c : α) (h : c + b = a) : a + -b = c :=
begin
rw -h,
simp
end

lemma neg_add_pos [add_comm_group α] (a b c : α) (h : c + a = b) : -a + b = c :=
begin
rw -h,
simp
end

lemma neg_zero [add_group α] (a : α) (h : a = 0) : - a = 0 :=
begin rw h, simp end

lemma nat_sub_zero {a b c d: ℕ} (hac : a = c) (hbd : b = d) (hcd : c < d) : a - b = 0 :=
begin
 simp_using_hs, apply nat.sub_eq_zero_of_le, apply le_of_lt, assumption
end

lemma nat_sub_pos (a b c d e : ℕ) (hac : a = c) (hbd : b = d) (hced : e + d = c) : a - b = e :=
begin
simp_using_hs, rw [-hced, nat.add_sub_cancel]
end

lemma mul_zero [mul_zero_class α] (a : α) : a * zero = zero :=
by simp

lemma zero_mul [mul_zero_class α] (a : α) : zero * a = zero :=
by simp

lemma one_mul_any [monoid α] (a a' : α) (h : a = a') : one * a = a' :=
by { rw -h, simp }

lemma any_mul_one [monoid α] (a a' : α) (h : a = a') : a * one = a' :=
by { rw -h, simp }

lemma subst_into_prod [has_mul α] (l r tl tr t : α) (prl : l = tl) (prr : r = tr) (prt : tl * tr = t) : l * r = t :=
by simp [prl, prr, prt]

lemma neg_mul_pos [has_mul α] [has_neg α] (a b c : α) (h : a * b = c) : -a * b = -c := sorry
lemma pos_mul_neg [has_mul α] [has_neg α] (a b c : α) (h : a * b = c) : a * -b = -c := sorry
lemma neg_mul_neg [has_mul α] [has_neg α] (a b c : α) (h : a * b = c) : -a * -b = c := sorry

lemma bit0_mul_any [distrib α] [has_one α] (a b c : α) (h : a * b = c) : bit0 a * b = bit0 c :=
begin
  unfold bit0,
  rewrite -h,
  rewrite right_distrib,
end

lemma any_mul_bit0 [semiring α] (a b c : α) (h : a * b = c) : a * bit0 b = bit0 c :=
by { rw -(bit0_mul_any a b c h), simp }

lemma any_mul_bit1 [semiring α] (a b s t : α) (hs : a * b = s) (ht : bit0 s + a  = t) :
        a * (bit1 b) = t :=
by simp [hs, ht]

lemma bit1_mul_any [semiring α] (a b s t : α) (hs : a * b = s) (ht : bit0 s + b  = t) :
        (bit1 a) * b = t :=
by simp [hs, ht]

end lemmas
end numeric.normalizer
