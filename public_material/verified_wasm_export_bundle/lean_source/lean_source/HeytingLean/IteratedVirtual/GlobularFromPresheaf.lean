import HeytingLean.IteratedVirtual.Globular
import HeytingLean.IteratedVirtual.GlobularPresheaf

/-!
# IteratedVirtual.GlobularFromPresheaf

Bridge: a presheaf-based globular set `GlobularSetPsh` induces the earlier minimal structured
`GlobularSet` record.

This keeps the existing IteratedVirtual code working while allowing future modules to treat
globular sets “canonically” as presheaves on `GlobularIndex`.
-/

namespace HeytingLean
namespace IteratedVirtual

open CategoryTheory

/-- Forget a presheaf globular set to the minimal structured `GlobularSet` interface. -/
def GlobularSetPsh.toGlobularSet (X : GlobularSetPsh) : GlobularSet where
  Cell := fun n => X.obj (Opposite.op (GlobularIndex.ofNat n))
  src := fun {n} => X.map (GlobularIndex.src n).op
  tgt := fun {n} => X.map (GlobularIndex.tgt n).op
  src_src_eq_src_tgt := by
    intro n x
    simpa [GlobularSetPsh.src, GlobularSetPsh.tgt, Functor.map_comp] using
      GlobularSetPsh.src_src_eq_src_tgt (X := X) (n := n) x
  tgt_src_eq_tgt_tgt := by
    intro n x
    simpa [GlobularSetPsh.src, GlobularSetPsh.tgt, Functor.map_comp] using
      GlobularSetPsh.tgt_src_eq_tgt_tgt (X := X) (n := n) x

namespace GlobularSetPsh

@[simp] theorem toGlobularSet_Cell (X : GlobularSetPsh) (n : Nat) :
    (X.toGlobularSet).Cell n = X.obj (Opposite.op (GlobularIndex.ofNat n)) :=
  rfl

@[simp] theorem toGlobularSet_src (X : GlobularSetPsh) (n : Nat) (x : X.obj (Opposite.op (GlobularIndex.ofNat (n + 1)))) :
    (X.toGlobularSet).src x = X.map (GlobularIndex.src n).op x :=
  rfl

@[simp] theorem toGlobularSet_tgt (X : GlobularSetPsh) (n : Nat) (x : X.obj (Opposite.op (GlobularIndex.ofNat (n + 1)))) :
    (X.toGlobularSet).tgt x = X.map (GlobularIndex.tgt n).op x :=
  rfl

end GlobularSetPsh

end IteratedVirtual
end HeytingLean

