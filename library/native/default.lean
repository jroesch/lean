import init.meta.format
import init.meta.expr
import init.string
import system.IO
import system.result
import native.ir
import native.format

namespace native

-- builtin stuff
meta constant is_internal_cnstr : expr → option unsigned
meta constant is_internal_cases : expr → option unsigned
meta constant is_internal_proj : expr → option unsigned
meta constant get_nat_value : expr → option nat

inductive error
| string : string -> error

attribute [reducible]
definition result (A : Type*) :=
  system.result error A

definition mk_error {T} : string -> result T :=
  fun s, system.result.err $ error.string s

definition mk_nat_literal (n : nat) : result ir.expr :=
  return (ir.expr.lit $ ir.literal.nat n)

-- HELPERS --
definition assert_name : ir.expr → result name
| (ir.expr.locl n) := system.result.ok n
| (ir.expr.call _ _) := mk_error "expected name, found: call "
| (ir.expr.lit _) := mk_error "expected name, found: lit "
| (ir.expr.mk_object _ _) := mk_error "expected name, found: obj "
| (ir.expr.global _) := mk_error "expected local, found global"
| (ir.expr.block _) := mk_error "expected local, found block"
| (ir.expr.project _ _) := mk_error "expected name, found project"
| (ir.expr.panic _) := mk_error "expected name, found panic"

meta definition mk_local (n : name) : expr :=
  expr.local_const n n binder_info.default (expr.const n [])

definition mk_call (head : name) (args : list ir.expr) : result ir.expr :=
  let args'' := list.map assert_name args
  in do args' <- monad.sequence args'',
  system.result.ok $ ir.expr.call head args'

meta definition mk_object (arity : unsigned) (args : list ir.expr) : result ir.expr :=
  let args'' := list.map assert_name args
  in do args' <- monad.sequence args'',
        system.result.ok $ ir.expr.mk_object (unsigned.to_nat arity) args'

meta definition is_return (n : name) : bool :=
  decidable.to_bool $ `native_compiler.return = n

meta definition one_or_error (args : list expr) : result expr :=
match args with
| ((h : expr) :: []) := system.result.ok h
| _ := mk_error "internal invariant violated, should only have one argument"
end

meta def panic (msg : string) : result ir.expr :=
  return $ ir.expr.panic msg

-- END HELPERS --

meta def compile_case (case : expr) : result ir.expr :=
  mk_error "failed to make case"

meta def compile_cases_on_to_ir_expr
    (scrutinee : name)
    (cases : list expr)
    (action : expr -> result ir.expr) : result ir.expr := do
    default <- panic "default case should never be reached",
    return (ir.expr.block $ (ir.stmt.switch scrutinee [] (ir.stmt.e default)))

-- this code isnt' great working around the semi-functional frontend
meta definition compile_expr_app_to_ir_expr
  (head : expr)
  (args : list expr)
  (action : expr -> result ir.expr) : result ir.expr := do
    args' <- monad.sequence $ list.map action args,
    if expr.is_constant head = bool.tt
    then if is_return (expr.const_name head) = bool.tt
    then do
      rexp <- one_or_error args,
      (ir.expr.block ∘ ir.stmt.return) <$> action rexp
    else match is_internal_cnstr head with
    | option.some n := mk_object n args'
    | option.none := match is_internal_cases head with
    | option.some n := compile_cases_on_to_ir_expr (expr.const_name head) args action
    | option.none := mk_call (expr.const_name head) args'
    end end
    else (mk_error ("unsupported call position" ++ (to_string head)))

meta definition compile_expr_macro_to_ir_expr (e : expr) : result ir.expr :=
  match native.get_nat_value e with
  | option.none := mk_error "unsupported macro"
  | option.some n := mk_nat_literal n
  end

meta definition compile_local (n : name) : result name :=
  return $ (mk_str_name "_$local$_" (name.to_string_with_sep "_" n))

meta definition compile_expr_to_ir_expr : expr → result ir.expr
| (expr.const n ls) :=
  match native.is_internal_cnstr (expr.const n ls) with
  | option.none := pure $ ir.expr.global n
  | option.some arity := pure $ ir.expr.mk_object (unsigned.to_nat arity) []
  end
| (expr.var i) := mk_error "there should be no bound variables in compiled terms"
| (expr.sort _) := mk_error "found sort"
| (expr.mvar _ _) := mk_error "unexpected meta-variable in expr"
| (expr.local_const n _ _ _) := ir.expr.locl <$> compile_local n
| (expr.app f x) :=
  let head := expr.get_app_fn (expr.app f x),
      args := expr.get_app_args (expr.app f x)
  in compile_expr_app_to_ir_expr head args compile_expr_to_ir_expr
| (expr.lam _ _ _ _) := mk_error "found lam"
| (expr.pi _ _ _ _) := mk_error "found pi"
| (expr.elet n _ v body) := mk_error "internal error: can not translate let binding into a ir_expr"
| (expr.macro d sz args) := compile_expr_macro_to_ir_expr (expr.macro d sz args)

meta definition compile_expr_to_ir_stmt : expr -> result ir.stmt
| (expr.pi _ _ _ _) := mk_error "found pi, should not be translating a Pi for any reason (yet ...)"
| (expr.elet n _ v body) := do
  n' <- compile_local n,
  v' <- compile_expr_to_ir_expr v,
  body' <- compile_expr_to_ir_stmt (expr.instantiate_vars body [mk_local n]),
  return (ir.stmt.letb n' v' body')
| e' := ir.stmt.e <$> compile_expr_to_ir_expr e'

meta definition get_arity : expr -> nat
| (expr.lam _ _ _ body) := 1 + get_arity body
| _ := 0

definition repeat {A : Type} : nat -> A -> list A
| 0 _ := []
| (n + 1) a := a :: repeat n a

definition zip {A B : Type} : list A → list B → list (A × B)
| [] [] := []
| [] (y :: ys) := []
| (x :: xs) [] := []
| (x :: xs) (y :: ys) := (x, y) :: zip xs ys

meta definition compile_decl_to_ir (decl_name : name) (args : list name) (body : expr) : result ir.decl := do
  system.result.and_then (compile_expr_to_ir_stmt body)
  (fun (body' : ir.stmt),
  let params := (zip args (repeat (list.length args) (ir.ty.ref ir.ty.object))) in
  pure (ir.decl.mk decl_name params ir.ty.object body'))

definition unwrap_or_else {T E : Type} : result T → (T → E) → (error -> E) -> E
| (system.result.err e) f err := err e
| (system.result.ok t) f err := f t

-- TODO: fix naming here
private meta definition take_arguments' : expr → list name → (list name × expr)
| (expr.lam n _ _ body) ns := take_arguments' body (n :: ns)
| e' ns := (ns, e')

meta definition take_arguments (e : expr) : (list name × expr) :=
  let res := take_arguments' e [],
      arg_names := prod.fst res,
      locals := list.map mk_local arg_names
  in (arg_names, expr.instantiate_vars (prod.snd res) (list.reverse locals))

meta definition compile_decl (decl_name : name) (e : expr) : format :=
  let arity := get_arity e,
      (args, body) := take_arguments e,
      ir := compile_decl_to_ir decl_name args body
  in unwrap_or_else ir format_cpp.decl (fun e, error.cases_on e (fun s, format.of_string s))

meta definition compile_rec : list (name × expr) → format
| [] := format.nil
| ((n, e) :: rest) := compile_decl n e ++ format.line ++ format.line ++ compile_rec rest

meta definition compile : list (name × expr) → format
| p := compile_rec p

end native
