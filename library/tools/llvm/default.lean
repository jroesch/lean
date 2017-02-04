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

meta constant module.write_to : string → module → io unit

end llvm
