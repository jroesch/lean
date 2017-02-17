import system.io

namespace llvm

/-- An LLVM context object. -/
meta constant context : Type

/-- Fetches the global LLVM context. -/
meta constant global_context : io context

/-- A LLVM module object. -/
meta constant module : Type

/-- Creates a new LLVM module object -/
meta constant module.new : string → io module

/-- Should we try to write some definitions this way?
    Having names is nice documentation -/
meta constant module.write_to :
    forall (path : string), module → io unit

/- An LLVM function object. -/
meta constant function : Type

meta constant module.get_function : module → string → option function

meta constant function.new : module → string → io function

meta constant basic_block : Type

meta constant basic_block.new : string → option function → option basic_block → io basic_block

end llvm
