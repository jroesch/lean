prelude
import init.meta.tactic
import init.meta.simp_tactic
import init.meta.defeq_simp_tactic
import init.meta.rewrite_tactic
import init.meta.expr
import init.meta.unfold_tactic
import init.monad
import init.list
import init.combinator
import init.wf
import init.relation
import init.meta.injection_tactic
import init.measurable
import init.applicative

namespace backend

-- inductive ir_exp :=
--   | dummy

-- inductive ir_stmt :=
-- | ite : ir_exp -> ir_stmt -> ir_stmt
-- | switch : ir_expr ->

-- A Wadler-style pretty printer
inductive doc :=
| nil
| append : doc → doc → doc
| nest : nat → doc → doc
| text : string → doc
| line : doc
| group : doc → doc → doc

definition doc_size [semireducible] : doc → nat
| doc_size doc.nil := 1
| doc_size (doc.append d1 d2) := 1 + doc_size d1 + doc_size d2
| doc_size (doc.nest _ d) := 1 + doc_size d
| doc_size (doc.text s) := 1
| doc_size doc.line := 1
| doc_size (doc.group d1 d2) := 1 + doc_size d1 + doc_size d2

definition doc_wf [instance] : well_founded (nat.measure doc_size) :=
  nat.measure.wf doc_size

inductive simple_doc :=
  | nil
  | text : string → simple_doc → simple_doc
  | line : nat → simple_doc → simple_doc

definition empty : doc :=
  doc.nil

definition concat (a b : doc) : doc :=
  doc.append a b

definition nest (n : nat) (d : doc) :=
  doc.nest n d

definition text (s : string) :=
  doc.text s

definition line := doc.line

definition flatten : doc → doc
| flatten doc.nil := doc.nil
| flatten (doc.append x y) :=
  doc.append (flatten x) (flatten y)
| flatten (doc.nest n x) :=
  doc.nest n (flatten x)
| flatten (doc.text s) := doc.text s
| flatten doc.line := doc.text " "
| flatten (doc.group x y) :=
  flatten x

definition repeat {A} : nat -> A -> list A
| repeat 0 x := []
| repeat (nat.succ n) x := repeat n x

definition layout : simple_doc → string
| layout simple_doc.nil := ""
| layout (simple_doc.text s d) := s ++ layout d
| layout (simple_doc.line i x) := '\n' :: (repeat i ' ' ++ layout x)

definition group (d : doc) := doc.group (flatten d) d

definition sum [reducible] : list nat -> nat
| sum [] := 0
| sum (x :: xs) := x + sum xs

definition list_doc_measure : list (ℕ × doc) → nat :=
  fun xs, sum (list.map (fun x, doc_size (prod.pr2 x)) xs)

definition fits (w : nat) : nat → simple_doc → bool
| fits k simple_doc.nil :=
  if w < k
  then bool.ff
  else bool.tt
| fits k (simple_doc.text s d') :=
  if w < k
  then bool.ff
  else fits (k + list.length s) d'
| fits k (simple_doc.line i d') :=
  if w < k
  then bool.ff
  else bool.tt

definition better (w k : nat) (x y : simple_doc) : simple_doc :=
  bool.cases_on (fits w k x) x y

definition pair_list_doc_measure (p : nat × list (nat × doc)) : nat :=
  list_doc_measure (prod.pr2 p)

definition docpair_wf [instance] : well_founded (nat.measure pair_list_doc_measure) :=
  nat.measure.wf pair_list_doc_measure

definition is_simple (d : doc) : Prop :=
  match d with
  | doc.nil := true
  | doc.text _ := true
  | doc.line := true
  | doc.group d1 d2 := true
  | _ := false
  end


check subtype

open tactic

meta_definition is_simple_tac : tactic unit := do
  unfold [`backend.is_simple],
  constructor

-- Ideally use wf-recursion to keep the implmentation clean, and generate good code for it.
definition be_flatten : nat → doc → list (nat × (subtype is_simple))
| be_flatten i doc.nil := []
| be_flatten i (doc.append d1 d2) := (be_flatten i d1) ++ (be_flatten i d2)
| be_flatten i (doc.nest j d) := be_flatten (i + j) d
| be_flatten i (doc.text s) := (i, subtype.tag (doc.text s) (by is_simple_tac)) :: []
| be_flatten i (doc.line) := (i, subtype.tag (doc.line) (by is_simple_tac)) :: []
| be_flatten i (doc.group d1 d2) := (i, subtype.tag (doc.group d1 d2) (by is_simple_tac)) :: []

print inductive subtype

definition subtype_is_simple_rec {C : doc → Type}
  (nil : C (doc.nil))
  (text : forall s, C (doc.text s))
  (line : C (doc.line))
  (group : forall d1 d2, C (doc.group d1 d2)) : forall (sd : subtype is_simple), C (subtype.elt_of sd) :=
by do
  intros,
  return unit.star

definition be' : nat → nat → list (nat × (subtype is_simple)) → simple_doc := by do
  intros,
  refine (@subtype_is_simple_rec (fun x, simple_doc))

-- definition be (w k : nat) (l : list (nat × doc)) : simple_doc :=
--   be' w (k, l)
--   -- | _ := simple_doc.nil
--   -- end

-- definition best (w k : nat) (d : doc) : simple_doc :=
--    be w k [(0, x)]

meta_definition compiler (e : expr) : string := to_string e

end backend
