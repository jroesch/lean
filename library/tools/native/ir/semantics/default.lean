import ..syntax
import .map

def addr := nat

inductive value
| object : nat → list addr → value
| closure : nat → list addr → addr → value
| array : list value → value
| fn : ir.defn → value

def value.project (obj : value) (field_no : nat) : option value := none

def env := map ir.symbol addr
def heap := map addr value

-- namespace expr

-- -- inductive object
-- -- | tag : nat → list object → object
-- -- | closure : ir.symbol → list object → object
-- -- | simple : int → object

-- -- def mk_literal_value : ir.literal → value
-- -- | nat : nat → literal
-- -- | integer : int → literal
-- -- | string : string → literal
-- -- -- I think these two can be unified
-- -- | binary : string → literal
-- -- -- This constructor is a hack, there is a bug with
-- -- -- the nested inductive compiler.
-- -- | symbol : symbol → literal
-- -- | array : list literal → literal

-- def mk_object_value (e : env) (tag : nat) (fs : list ir.symbol) : value :=

-- inductive expr.eval : env → heap → ir.expr → value → Prop
-- | global : ∀ e h g, expr.eval e h (ir.expr.global g) (e.get g >>= h.get)
-- -- | lit : ∀ e h l, expr.eval e h (ir.expr.lit l) (mk_literal_value l)
-- | mk_object : ∀ e h n fs, expr.eval e h (ir.expr.mk_object n fs) (mk_object_value e n fs)
-- | sym : ∀ e h s, expr.eval e h (ir.expr.sym s) (sorry)
-- | project : ∀ e h n field_no, expr.eval e h (ir.expr.project n field_no) (e.get n >>= h.get >>= (fun o, value.project o field_no))
-- -- | mk_native_closure : symbol → nat → list symbol → expr
-- -- | invoke : symbol → list symbol → expr
-- -- | uninitialized : expr
-- -- | constructor : symbol → list symbol → expr
-- -- | address_of : symbol → expr
-- -- -- these need to be literal/values/etc
-- -- | binary_operator : op → expr → expr → expr
-- | array : ∀ e h elems, expr.eval e h (ir.expr.array elems) none
-- -- | call : ∀ e h fn df
-- --     e.get fn = some fn_addr →
-- --     h.get fn_addr = some (fn df) →
-- --     expr.eval

-- -- -- lemma eval_expr_pure :
-- -- --     forall e h exp val,
-- -- --         expr.eval e h exp (some val)

-- -- -- def expr.const_eval :
-- -- end expr
