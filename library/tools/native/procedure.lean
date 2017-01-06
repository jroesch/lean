/-
Copyright (c) 2016 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/

import init.meta.name
import init.meta.expr

@[reducible] meta def procedure :=
  name × expr

inductive extern_fn
| mk : bool → name → name → unsigned → extern_fn

meta def procedure.to_string : procedure → string
| (n, e) := "def " ++ to_string n ++ " := \n" ++ to_string e

meta def procedure.map_body (f : expr → expr) : procedure → procedure
| (n, e) := (n, f e)

meta instance : has_to_string procedure :=
  ⟨ procedure.to_string ⟩
