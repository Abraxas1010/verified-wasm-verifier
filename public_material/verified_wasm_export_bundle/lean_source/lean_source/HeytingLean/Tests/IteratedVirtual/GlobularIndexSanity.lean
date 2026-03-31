import HeytingLean.IteratedVirtual.GlobularPresheaf

/-!
# Tests.IteratedVirtual.GlobularIndexSanity

Compile-only checks for Phase 7 “true globular semantics”:
- explicit globular indexing category `GlobularIndex`,
- presheaf globular sets `GlobularSetPsh`,
- walking globes as representables `GlobePsh`,
- k-cells as globe-maps `GlobePsh k ⟶ X`.
-/

namespace HeytingLean
namespace Tests
namespace IteratedVirtual

open HeytingLean.IteratedVirtual

#check HeytingLean.IteratedVirtual.GlobularIndex.Obj
#check HeytingLean.IteratedVirtual.GlobularSetPsh
#check HeytingLean.IteratedVirtual.GlobePsh
#check HeytingLean.IteratedVirtual.kCellPsh

-- The induced source/target operations satisfy the globular identities.
example {X : GlobularSetPsh} {n : Nat} (x : GlobularSetPsh.Cell X (n + 2)) :
    GlobularSetPsh.src (n := n) (GlobularSetPsh.src (n := n + 1) x) =
      GlobularSetPsh.src (n := n) (GlobularSetPsh.tgt (n := n + 1) x) :=
  GlobularSetPsh.src_src_eq_src_tgt (n := n) x

example {X : GlobularSetPsh} {n : Nat} (x : GlobularSetPsh.Cell X (n + 2)) :
    GlobularSetPsh.tgt (n := n) (GlobularSetPsh.src (n := n + 1) x) =
      GlobularSetPsh.tgt (n := n) (GlobularSetPsh.tgt (n := n + 1) x) :=
  GlobularSetPsh.tgt_src_eq_tgt_tgt (n := n) x

end IteratedVirtual
end Tests
end HeytingLean
