/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Notation for intervals and some properties.

The mnemonic: o = open, c = closed, u = unbounded. For example, Iou a b is '(a, ∞).
-/
import .order data.set
open set

-- TODO: move
section
  open set

end

namespace interval

section order_pair
variables {A : Type} [order_pair A]

definition Ioo (a b : A) : set A := {x | a < x ∧ x < b}
definition Ioc (a b : A) : set A := {x | a < x ∧ x ≤ b}
definition Ico (a b : A) : set A := {x | a ≤ x ∧ x < b}
definition Icc (a b : A) : set A := {x | a ≤ x ∧ x ≤ b}
definition Iou (a : A)   : set A := {x | a < x}
definition Icu (a : A)   : set A := {x | a ≤ x}
definition Iuo (b : A)   : set A := {x | x < b}
definition Iuc (b : A)   : set A := {x | x ≤ b}

notation `'(` a `, ` b `)`     := Ioo a b
notation `'(` a `, ` b `]`     := Ioc a b
notation `'[` a `, ` b `)`     := Ico a b
notation `'[` a `, ` b `]`     := Icc a b
notation `'(` a `, ` `∞` `)`   := Iou a
notation `'[` a `, ` `∞` `)`   := Icu a
notation `'(` `-∞` `, ` b `)`  := Iuo b
notation `'(` `-∞` `, ` b `]`  := Iuc b

variables a b : A

proposition Iou_inter_Iuo : '(a, ∞) ∩ '(-∞, b) = '(a, b) := rfl
proposition Icu_inter_Iuo : '[a, ∞) ∩ '(-∞, b) = '[a, b) := rfl
proposition Iou_inter_Iuc : '(a, ∞) ∩ '(-∞, b] = '(a, b] := rfl
proposition Ioc_inter_Iuc : '[a, ∞) ∩ '(-∞, b] = '[a, b] := rfl

proposition Icc_self : '[a, a] = '{a} :=
set.ext (take x, iff.intro
  (suppose x ∈ '[a, a],
    have x = a, from le.antisymm (and.right this) (and.left this),
    show x ∈ '{a}, from mem_singleton_of_eq this)
  (suppose x ∈ '{a},
    have x = a, from eq_of_mem_singleton this,
    show a ≤ x ∧ x ≤ a, from and.intro (eq.subst this !le.refl) (eq.subst this !le.refl)))

end order_pair

section decidable_linear_order

variables {A : Type} [decidable_linear_order A]

proposition Icc_eq_Icc_union_Ioc {a b c : A} (H1 : a ≤ b) (H2 : b ≤ c) :
  '[a, c] = '[a, b] ∪ '(b, c] :=
set.ext (take x, iff.intro
  (assume H3 :  x ∈ '[a, c],
    decidable.by_cases
      (suppose x ≤ b,
         or.inl (and.intro (and.left H3) this))
      (suppose ¬ x ≤ b,
         or.inr (and.intro (lt_of_not_ge this) (and.right H3))))
  (suppose x ∈ '[a, b] ∪ '(b, c],
    or.elim this
      (suppose x ∈ '[a, b],
         and.intro (and.left this) (le.trans (and.right this) H2))
      (suppose x ∈ '(b, c],
         and.intro (le_of_lt (lt_of_le_of_lt H1 (and.left this))) (and.right this))))

end decidable_linear_order

/- intervals of natural numbers -/

namespace nat
open nat eq.ops
  variables m n : ℕ

  proposition Ioc_eq_Icc_succ : '(m, n] = '[succ m, n] := rfl

  proposition Ioo_eq_Ico_succ : '(m, n) = '[succ m, n) := rfl

  proposition Ico_succ_eq_Icc : '[m, succ n) = '[m, n] :=
  set.ext (take x, iff.intro
    (assume H, and.intro (and.left H) (le_of_lt_succ (and.right H)))
    (assume H, and.intro (and.left H) (lt_succ_of_le (and.right H))))

  proposition Ioo_succ_eq_Ioc : '(m, succ n) = '(m, n] :=
  set.ext (take x, iff.intro
    (assume H, and.intro (and.left H) (le_of_lt_succ (and.right H)))
    (assume H, and.intro (and.left H) (lt_succ_of_le (and.right H))))

  proposition Icu_zero : '[(0 : nat), ∞) = univ :=
  eq_univ_of_forall (take x, zero_le x)

  proposition Icc_zero (n : ℕ) : '[0, n] = '(-∞, n] :=
  have '[0, n] = '[0, ∞) ∩ '(-∞, n], from rfl,
  by+ rewrite [this, Icu_zero, univ_inter]

  proposition bij_on_add_Icc_zero (m n : ℕ) : bij_on (add m) ('[0, n]) ('[m, m+n]) :=
  have mapsto : ∀₀ i ∈ '[0, n], m + i ∈ '[m, m+n], from
    (take i, assume imem,
      have H1 : m ≤ m + i, from !le_add_right,
      have H2 : m + i ≤ m + n, from add_le_add_left (and.right imem) m,
      show m + i ∈ '[m, m+n], from and.intro H1 H2),
  have injon : inj_on (add m) ('[0, n]), from
    (take i j, assume Hi Hj H, !eq_of_add_eq_add_left H),
  have surjon : surj_on (add m) ('[0, n]) ('[m, m+n]), from
    (take j, assume Hj : j ∈ '[m, m+n],
      obtain lej jle, from Hj,
      let i := j - m in
      have ile : i ≤ n, from calc
        j - m ≤ m + n - m : nat.sub_le_sub_right jle m
          ... = n         : nat.add_sub_cancel_left,
      have iadd : m + i = j, by rewrite add.comm; apply nat.sub_add_cancel lej,
      exists.intro i (and.intro (and.intro !zero_le ile) iadd)),
  bij_on.mk mapsto injon surjon
end nat

section nat -- put the instances in the intervals namespace
open nat eq.ops
  variables m n : ℕ

  proposition nat.Iuc_finite [instance] (n : ℕ) : finite '(-∞, n] :=
  nat.induction_on n
    (have '(-∞, 0] ⊆ '{0}, from λ x H, mem_singleton_of_eq (le.antisymm H !zero_le),
      finite_subset this)
    (take n, assume ih : finite '(-∞, n],
      have '(-∞, succ n] ⊆ '(-∞, n] ∪ '{succ n},
        by intro x H; rewrite [mem_union_iff, mem_singleton_iff]; apply le_or_eq_succ_of_le_succ H,
        finite_subset this)

  proposition nat.Iuo_finite [instance] (n : ℕ) : finite '(-∞, n) :=
  have '(-∞, n) ⊆ '(-∞, n], from λ x, le_of_lt,
  finite_subset this

  proposition nat.Icc_finite [instance] (m n : ℕ) : finite ('[m, n]) :=
  have '[m, n] ⊆ '(-∞, n], from λ x H, and.right H,
  finite_subset this

  proposition nat.Ico_finite [instance] (m n : ℕ) : finite ('[m, n)) :=
  have '[m, n) ⊆ '(-∞, n), from λ x H, and.right H,
  finite_subset this

  proposition nat.Ioc_finite [instance] (m n : ℕ) : finite '(m, n] :=
  have '(m, n] ⊆ '(-∞, n], from λ x H, and.right H,
  finite_subset this
end nat

end interval
