import system.io

set_option trace.native_compiler true
set_option trace.compiler true

definition main : io unit :=
  do { n ← return (10:nat),
   if n = (11:nat) then
     put_nat 1
  else
     put_nat 2 }

-- vm_eval main
