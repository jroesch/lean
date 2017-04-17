prelude

import init.algebra.field init.algebra.ordered_ring
import init.data.nat.lemmas
import init.data.int

namespace numeric
namespace lemmas

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

lemma bit1_congr [has_add α] [has_one α] (bits bits' : α) : bits = bits' → bit1 bits = bit1 bits' :=
begin
    intros,
    rw a,
end

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

lemma bit0_add_bit0 [add_comm_semigroup α] [has_one α] (a b r : α) (h : a + b = r) : bit0 a + bit0 b = bit0 r :=
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

lemma bit1_add_bit1 [add_comm_semigroup α] [has_one α] (a b r : α) (h : a + b = r) : bit1 a + bit1 b = bit0 (r + 1) :=
begin
  unfold bit1 bit0,
  rw -h,
  simp,
end

end lemmas
end numeric
