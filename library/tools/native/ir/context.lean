import tools.native.ir.syntax

namespace native
namespace ir

meta structure context :=
(items : rb_map name ir.item)

meta def context.new
(decls : list ir.decl)
(defns : list ir.defn)
(types : list ir.type_decl) : context :=
do let items := defns.map ir.item.defn ++ decls.map ir.item.decl,
   let named_items := items.map (fun i, (ir.item.get_name i, i)),
   context.mk $ rb_map.of_list named_items

meta def context.lookup_item (ctxt : context) (n : name) : option ir.item :=
rb_map.find (context.items ctxt) n

meta def context.extend_items : rb_map name ir.item → list (name × ir.item) → rb_map name ir.item
| items [] := items
| items ((n, i) :: bs) :=
  context.extend_items (items.insert n i) bs

meta def context.extend (ctx : context) (new_items : list (name × ir.item)) : context :=
match ctx with
| ⟨ items ⟩ := ⟨ context.extend_items items new_items ⟩
end

meta def context.to_items (ctx : context) : list ir.item :=
list.map prod.snd $ ctx.items.to_list

meta def context.get_main_fn (ctxt : context) : option ir.item :=
ctxt.lookup_item "___lean__main"

end ir
end native
