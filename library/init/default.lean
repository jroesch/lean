/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.core init.logic init.category init.data.basic
import init.propext init.cc_lemmas init.funext init.category.combinators init.function init.classical
import init.util init.coe init.wf init.meta init.algebra init.data

def debugger.attr : user_attribute :=
{ name  := `breakpoint,
  descr := "breakpoint for debugger" }

run_command attribute.register `debugger.attr
