import tools.llvm
import .ir
import system.io

namespace native

namespace llvm

meta def format_concat : list format → format
| [] := format.nil
| (f :: fs) := f ++ format_concat fs

meta def comma_sep (items : list format) : format :=
format_concat
  (list.intersperse (format.of_string "," ++ format.space) items)

def one_of (c : char) (s : string) : bool := bool.ff

def replace (c : char) (replacement : string) : string -> string
| [] := []
| (s :: ss) :=
  if c = s
  then replacement ++ replace ss
  else s :: replace ss

meta def mangle_external_name (n : name) : string :=
  name.to_string_with_sep "_" n

meta def mangle_name (n : name) : string :=
  (replace #"'" "_$single_quote$_" $ name.to_string_with_sep "$dot$_" n)

meta def mangle_symbol : ir.symbol → string
| (ir.symbol.name n) := "_$lean$_" ++ mangle_name n
| (ir.symbol.external opt_ns n) :=
  match opt_ns with
  | some ns := to_string ns ++ "::" ++ mangle_external_name n
  | none := mangle_external_name n
  end

meta def compile_defn (mod : llvm.module) : ir.defn → io unit
| (ir.defn.mk ext n params ret body) := do
    fn ← llvm.function.new mod (mangle_symbol n),
    bb <- llvm.basic_block.new "entry" (some fn) none,
    builder <- llvm.ir_builder.new,
    builder^.set_insert_point bb,
    builder^.create_ret_void,
    return ()

-- def moduleM :=
meta def compile_item (mod : llvm.module) : ir.item → io unit
| (ir.item.defn defn) := compile_defn mod defn
| _ := return ()

meta def compile_items (mod : llvm.module) : list ir.item → io unit
| [] := return ()
| (i :: is) := do
  compile_item mod i,
  compile_items is,
  return ()

end llvm

/-- This will transform an ir.context into an LLVM module,
    configure the appropriate settings and generate an
    executable using the LLVM module. -/
@[inline] meta def llvm_compiler (ctxt : native.ir.context) : io unit := do
    mod <- llvm.module.new "native_code",
    llvm.module.write_to "out.ll" mod,
    -- this line triggers a compiler error,
    -- monad.mapm (fun i, llvm.compile_item mod i) ctxt^.to_items,
    llvm.compile_items mod ctxt^.to_items,
    return ()

end native
