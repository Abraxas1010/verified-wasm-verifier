import HeytingLean.IteratedVirtual.GlobularFromPresheaf
import HeytingLean.IteratedVirtual.GlobularToPresheaf

/-!
# IteratedVirtual.GlobularRoundTrip

Phase‑8 strict-only hygiene: show that the structured→presheaf→structured round-trip is faithful
on the **globular data** (cells + src/tgt), and package it as an isomorphism in `GlobularSet`.

Notes:
- This is a local lemma about the current `GlobularIndex` encoding and the current
  `GlobularSet.toPresheaf` choice of “downward” maps (`downSrc`/`downTgt`).
- This does **not** claim any weak `Catₙ` semantics.
-/

namespace HeytingLean
namespace IteratedVirtual

open CategoryTheory

namespace GlobularSet

universe u

@[simp] theorem downSrc_succ (X : GlobularSet.{u}) (n : Nat) (x : X.Cell (n + 1)) :
    downSrc X n (n + 1) (Nat.le_succ n) x = X.src x := by
  simp [downSrc]

@[simp] theorem downTgt_succ (X : GlobularSet.{u}) (n : Nat) (x : X.Cell (n + 1)) :
    downTgt X n (n + 1) (Nat.le_succ n) x = X.tgt x := by
  simp [downTgt]

@[simp] theorem toPresheaf_map_src (X : GlobularSet.{u}) (n : Nat) (x : X.Cell (n + 1)) :
    (X.toPresheaf).map (GlobularIndex.src n).op x = X.src x := by
  simp [GlobularSet.toPresheaf, GlobularSet.toPresheafMap, GlobularIndex.src, GlobularIndex.Hom.src]

@[simp] theorem toPresheaf_map_tgt (X : GlobularSet.{u}) (n : Nat) (x : X.Cell (n + 1)) :
    (X.toPresheaf).map (GlobularIndex.tgt n).op x = X.tgt x := by
  simp [GlobularSet.toPresheaf, GlobularSet.toPresheafMap, GlobularIndex.tgt, GlobularIndex.Hom.tgt]

@[simp] theorem toPresheaf_toGlobularSet_src (X : GlobularSet.{u}) (n : Nat) (x : X.Cell (n + 1)) :
    ((X.toPresheaf).toGlobularSet).src x = X.src x := by
  simp [GlobularSetPsh.toGlobularSet_src]

@[simp] theorem toPresheaf_toGlobularSet_tgt (X : GlobularSet.{u}) (n : Nat) (x : X.Cell (n + 1)) :
    ((X.toPresheaf).toGlobularSet).tgt x = X.tgt x := by
  simp [GlobularSetPsh.toGlobularSet_tgt]

/-- Structured→presheaf→structured is (canonically) isomorphic to the original `GlobularSet`. -/
def toPresheaf_toGlobularSetIso (X : GlobularSet.{u}) : (X.toPresheaf).toGlobularSet ≅ X where
  hom :=
    { map := fun _ x => x
      map_src := by intro n x; simp
      map_tgt := by intro n x; simp }
  inv :=
    { map := fun _ x => x
      map_src := by intro n x; simp
      map_tgt := by intro n x; simp }
  hom_inv_id := by
    apply Hom.ext
    intro n x
    rfl
  inv_hom_id := by
    apply Hom.ext
    intro n x
    rfl

end GlobularSet

end IteratedVirtual
end HeytingLean
