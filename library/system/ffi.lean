import system.io


namespace ffi

-- Be careful when changing this, there is a corresponding enum in `vm_ptr.cpp` which
-- corresponds to the contructor numbering here.
inductive base_type
| int
| char

inductive type
-- A base type with sizing and alignment corresponding to C.
| base : base_type → type
-- A builtin array with a statically known size.
| array : nat -> type → type
-- | struct : struct_def -> type
| void : type

instance base_type_is_type : has_coe base_type type :=
⟨ λ bt, type.base bt ⟩

end ffi

structure ffi :=
(ref : ffi.type -> Type)
(base_size_of : ffi.base_type → nat)

definition is_sized : ffi.type → Prop
| is_sized (array _) := false
| is_sized _ := true

definition sizeof : Π (ty : ffi.type), is_sized ty -> nat
| sizeof (base bt) p := base_size_of bt
| sizeof (sized_array n t) p := n * sizeof t (array_T_sized_implies_T_sized t p)
| sizeof (array T) p := 0
| sizeof (void) p := 0

definition value_of : type → Type.{1}
  | value_of void := unit
  | value_of T := ptr T

-- attribute [reducible] value_of

-- A special marker for converting
definition extern (ret : type) (s : string) : list type -> Type.{1}
  | extern [] := IO (value_of ret)
  | extern (t :: ts) := (value_of t) -> extern ts
