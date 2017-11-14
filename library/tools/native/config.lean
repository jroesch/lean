/-
Copyright (c) 2017 Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jared Roesch
-/

import .internal

namespace native

structure config :=
(debug : bool := bool.ff)
(backend : string := "c++")
(include_path : list string)
(library_path : list string)

open tactic

-- TODO(@jroesch) do path parsing here
meta def parse_path_var (str : string) : list string :=
[str].filter (fun s, s ≠ "")

meta def load_config : tactic config :=
do opts ← get_options,
   let lib_path := opts.get_string `native.library_path "" ,
   let inc_path := opts.get_string `native.include_path "",
   let backend := opts.get_string `native.backend "c++",
   let lib_path := parse_path_var lib_path ++ [get_install_path ++ "lib"],
   let inc_path := parse_path_var inc_path ++  [get_install_path ++ "include/lean_ext"],
   -- tactic.trace $ "IncludePath: " ++ to_string inc_path,
   -- tactic.trace $ "LibraryPath: " ++ to_string lib_path,
   -- tactic.trace get_install_path,
   return {
     library_path := lib_path,
     include_path := inc_path,
     backend := backend,
  }

end native
