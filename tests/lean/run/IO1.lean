import system.io
open list

-- set_option pp.all true

set_option trace.native_compiler true

definition main : io unit :=
  do l₁ ← get_line,
     l₂ ← get_line,
     put_str (l₂ ++ l₁)

set_option trace.compiler.code_gen true
vm_eval main

vm_eval put_str "hello\n"

print "************************"

definition aux (n : nat) : io unit :=
  do put_str "========\nvalue: ",
     put_nat n,
     put_str "\n========\n"

vm_eval aux 20

print "************************"

definition repeat : nat → (nat → io unit) → io unit
| 0     a := return ()
| (n+1) a := do a n, repeat n a

vm_eval repeat 10 aux

print "************************"

definition execute : list (io unit) → io unit
| []      := return ()
| (x::xs) := do x, execute xs

vm_eval repeat 10 (λ i, execute [aux i, put_str "hello\n"])

print "************************"

vm_eval
  do n ← return 10,
     put_str "value: ",
     put_nat n,
     put_str "\n",
     put_nat (n+2),
     put_str "\n----------\n"

print "************************"
