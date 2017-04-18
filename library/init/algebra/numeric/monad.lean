prelude

import init.category.state

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

meta def normalize (e : expr) : normalizer_m (expr × expr) :=
do st ← state_t.read,
   st.normalizer e

meta def current_ty : normalizer_m expr :=
do st ← state_t.read,
   return $ st.current_ty
