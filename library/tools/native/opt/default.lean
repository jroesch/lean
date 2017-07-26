import tools.native.ir.context

namespace native
namespace opt

structure fn_pass :=
(transform : ir.item → option ir.item)

def fuse_fn_passes : list fn_pass → fn_pass
| [] := fn_pass.mk $ λ i, none
| (p :: ps) :=
    let kontp := fuse_fn_passes ps
    in fn_pass.mk $ λ i, p.transform i >>= kontp.transform

-- def optimize (passes : list fn_pass) (ctxt : ir.context) : ir.context :=
-- sorry

end opt
end native
