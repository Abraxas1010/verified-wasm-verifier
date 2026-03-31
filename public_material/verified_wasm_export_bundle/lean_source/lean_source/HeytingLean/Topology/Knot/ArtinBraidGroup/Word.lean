import HeytingLean.Topology.Knot.ArtinBraidGroup.Perm
import HeytingLean.Topology.Knot.Braid

/-!
# Artin braid group: bridge from executable braid words (Phase 6)

This file connects the executable braid-word layer (`HeytingLean.Topology.Knot.Braid`) to the
theorem-level Artin braid group `Bₙ` defined as a presented group.

Deliverables:
* a checked interpretation `wordToBraidGroup : List Braid.Gen → Except String (BraidGroup n)`;
* a checked permutation action of a braid word on strand indices;
* an alignment theorem: applying the canonical representation `Bₙ → Sₙ` to the interpreted word
  agrees with the direct permutation fold of adjacent transpositions.
 -/

namespace HeytingLean
namespace Topology
namespace Knot

namespace ArtinBraid

open PresentedGroup

open HeytingLean.Topology.Knot.Reidemeister
open HeytingLean.Topology.Knot.Braid

namespace Word

/-- Interpret a `Nat` generator index as an Artin generator `Fin (n-1)` if in range. -/
def genOfNat (n i : Nat) : Except String (Gen n) := do
  if h : i < n - 1 then
    return ⟨i, h⟩
  throw s!"braid generator out of range: i={i} (need i < n-1, n={n})"

/-- Interpret a signed executable braid generator as an element of the presented group `Bₙ`. -/
def ofGen (n : Nat) (g : Braid.Gen) : Except String (BraidGroup n) := do
  let i' ← genOfNat n g.i
  let s : BraidGroup n := sigma (n := n) i'
  return match g.sign with
    | .pos => s
    | .neg => s⁻¹

/-- Interpret an executable braid word as an element of the presented group `Bₙ`. -/
def toBraidGroup (n : Nat) : List Braid.Gen → Except String (BraidGroup n)
  | [] => pure 1
  | g :: gs => do
      let t ← ofGen n g
      let rest ← toBraidGroup n gs
      return t * rest

/-- Direct permutation action of an executable braid word on strand indices `Fin n`. -/
def toPerm (n : Nat) : List Braid.Gen → Except String (Equiv.Perm (Fin n))
  | [] => pure 1
  | g :: gs => do
      let i' ← genOfNat n g.i
      let τ := PermRep.sigmaPerm n i'
      let t :=
        match g.sign with
        | .pos => τ
        | .neg => τ⁻¹
      let rest ← toPerm n gs
      return t * rest

@[simp] theorem toPerm_nil (n : Nat) : toPerm n [] = (pure 1) := rfl
@[simp] theorem toBraidGroup_nil (n : Nat) : toBraidGroup n [] = (pure 1) := rfl

theorem toPerm_toBraidGroup (n : Nat) (w : List Braid.Gen) :
    (do
        let bg ← toBraidGroup n w
        return PermRep.toPerm (n := n) bg) =
      toPerm n w := by
  classical
  induction w with
  | nil =>
      simp [toBraidGroup, toPerm, Pure.pure, Except.pure, Bind.bind, Except.bind]
  | cons g gs ih =>
      cases g with
      | mk i sgn =>
          cases hgi : genOfNat n i with
          | error e =>
              -- Both computations fail on the same head check.
              simp [toBraidGroup, toPerm, ofGen, hgi, Bind.bind, Except.bind]
          | ok i' =>
              have htail :
                  (PermRep.toPerm (n := n)) <$> toBraidGroup n gs = toPerm n gs := by
                simpa using ih
              -- Split on the tail `toBraidGroup` result, and use `htail` to align the `toPerm` tail.
              cases hbg : toBraidGroup n gs with
              | error e =>
                  have htp : toPerm n gs = Except.error e := by
                    have htail' := htail
                    rw [hbg] at htail'
                    have hmap :
                        (PermRep.toPerm (n := n)) <$> (Except.error e : Except String (BraidGroup n)) =
                          (Except.error e : Except String (Equiv.Perm (Fin n))) := by
                      rfl
                    exact (hmap.symm.trans htail').symm
                  cases sgn <;>
                    simp [toBraidGroup, toPerm, ofGen, hgi, hbg, htp, Bind.bind, Except.bind, Pure.pure, Except.pure]
              | ok bg =>
                  have htp : toPerm n gs = Except.ok ((PermRep.toPerm (n := n)) bg) := by
                    have htail' := htail
                    rw [hbg] at htail'
                    have hmap :
                        (PermRep.toPerm (n := n)) <$> (Except.ok bg : Except String (BraidGroup n)) =
                          (Except.ok ((PermRep.toPerm (n := n)) bg) : Except String (Equiv.Perm (Fin n))) := by
                      rfl
                    exact (hmap.symm.trans htail').symm
                  cases sgn <;>
                    simp [toBraidGroup, toPerm, ofGen, hgi, hbg, htp, Bind.bind, Except.bind, Pure.pure, Except.pure, map_mul]

end Word

end ArtinBraid

end Knot
end Topology
end HeytingLean
