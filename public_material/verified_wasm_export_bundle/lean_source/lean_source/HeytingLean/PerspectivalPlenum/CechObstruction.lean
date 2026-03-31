import HeytingLean.PerspectivalPlenum.ContextualityEngine
import HeytingLean.PerspectivalPlenum.SheafLensCategory

namespace HeytingLean
namespace PerspectivalPlenum
namespace LensSheaf
namespace Cech

universe u v

/--
Čech H0 surrogate for the current finite-cover formalization:
an explicit global section whose restrictions match the family.
-/
def H0GlobalSections {A : Type u}
    (F : LensPresheaf A) (U : LensObj A) (C : CoveringFamily U)
    (m : MatchingFamily F U C) : Type u :=
  { s : F.obj (Opposite.op U) // ∀ i : C.I, F.map (Quiver.Hom.op (C.hom i)) s = m.sec i }

/-- H0 is nonempty iff gluing succeeds. -/
abbrev HasH0 {A : Type u}
    (F : LensPresheaf A) (U : LensObj A) (C : CoveringFamily U)
    (m : MatchingFamily F U C) : Prop :=
  Nonempty (H0GlobalSections F U C m)

/-- Čech H1 surrogate: obstruction to gluing over the chosen cover. -/
abbrev HasH1Obstruction {A : Type u}
    (F : LensPresheaf A) (U : LensObj A) (C : CoveringFamily U)
    (m : MatchingFamily F U C) : Prop :=
  ¬ Amalgamates F U C m

@[simp] theorem hasH0_iff_amalgamates {A : Type u}
    (F : LensPresheaf A) (U : LensObj A) (C : CoveringFamily U)
    (m : MatchingFamily F U C) :
    HasH0 F U C m ↔ Amalgamates F U C m := by
  constructor
  · intro h
    rcases h with ⟨⟨s, hs⟩⟩
    exact ⟨s, hs⟩
  · intro h
    rcases h with ⟨s, hs⟩
    exact ⟨⟨s, hs⟩⟩

theorem h1_of_no_amalgamation {A : Type u}
    (F : LensPresheaf A) (U : LensObj A) (C : CoveringFamily U)
    (m : MatchingFamily F U C)
    (hNo : ¬ Amalgamates F U C m) :
    HasH1Obstruction F U C m := hNo

theorem no_h1_of_h0 {A : Type u}
    (F : LensPresheaf A) (U : LensObj A) (C : CoveringFamily U)
    (m : MatchingFamily F U C)
    (h0 : HasH0 F U C m) :
    ¬ HasH1Obstruction F U C m := by
  intro h1
  exact h1 ((hasH0_iff_amalgamates F U C m).1 h0)

section Pair

variable {A : Type u}
variable (U : LensObj A)
variable (m : MatchingFamily (witnessPresheaf A) U (pairCover U))

/-- Pair-cover compatibility condition (agreement on overlap). -/
def PairCompatible : Prop := m.sec false = m.sec true

theorem pairCompatible_hasH0 (hCompat : PairCompatible U m) :
    HasH0 (witnessPresheaf A) U (pairCover U) m := by
  refine (hasH0_iff_amalgamates (witnessPresheaf A) U (pairCover U) m).2 ?_
  exact witnessPresheaf_pair_amalgamates_of_eq U m hCompat

theorem pairIncompatible_hasH1
    (hIncompat : ¬ PairCompatible U m) :
    HasH1Obstruction (witnessPresheaf A) U (pairCover U) m := by
  intro hAm
  rcases hAm with ⟨s, hs⟩
  have hs0 : s = m.sec false := by
    simpa [pairCover] using hs false
  have hs1 : s = m.sec true := by
    simpa [pairCover] using hs true
  exact hIncompat (hs0.symm.trans hs1)

end Pair

end Cech
end LensSheaf

namespace ContextualityEngine

/-- Classification of gluing/transport obstruction for ATP routing. -/
inductive CechObstructionClass where
  | none
  | h1_global_section
  | h1_overlap_incompatibility
  | dimensional_mismatch
  | nucleus_incompatibility
  deriving DecidableEq, Repr

/-- Degree tag used by routing/telemetry to prioritize strategies. -/
def cohomologyDegree : CechObstructionClass → Nat
  | .none => 0
  | .h1_global_section => 1
  | .h1_overlap_incompatibility => 1
  | .dimensional_mismatch => 1
  | .nucleus_incompatibility => 1

/-- H0 surrogate in contextuality space: global admissibility. -/
abbrev HasCechH0
    (X : Ctx) (cover : Finset Ctx)
    (e : HeytingLean.LoF.CryptoSheaf.Quantum.EmpiricalModel cover)
    (coverSubX : ∀ {C}, C ∈ cover → C ⊆ X) : Prop :=
  GloballyAdmissible X cover e coverSubX

/-- H1 surrogate in contextuality space: global obstruction. -/
abbrev HasCechH1
    (X : Ctx) (cover : Finset Ctx)
    (e : HeytingLean.LoF.CryptoSheaf.Quantum.EmpiricalModel cover)
    (coverSubX : ∀ {C}, C ∈ cover → C ⊆ X) : Prop :=
  GloballyObstructed X cover e coverSubX

@[simp] theorem hasCechH0_iff_globalAdmissible
    (X : Ctx) (cover : Finset Ctx)
    (e : HeytingLean.LoF.CryptoSheaf.Quantum.EmpiricalModel cover)
    (coverSubX : ∀ {C}, C ∈ cover → C ⊆ X) :
    HasCechH0 X cover e coverSubX ↔ GloballyAdmissible X cover e coverSubX :=
  Iff.rfl

@[simp] theorem hasCechH1_iff_globalObstructed
    (X : Ctx) (cover : Finset Ctx)
    (e : HeytingLean.LoF.CryptoSheaf.Quantum.EmpiricalModel cover)
    (coverSubX : ∀ {C}, C ∈ cover → C ⊆ X) :
    HasCechH1 X cover e coverSubX ↔ GloballyObstructed X cover e coverSubX :=
  Iff.rfl

/-- Triangle contextuality supplies a concrete nontrivial H1 witness. -/
theorem triangle_has_cech_h1 :
    HasCechH1
      HeytingLean.Quantum.Contextuality.Triangle.X
      HeytingLean.Quantum.Contextuality.Triangle.cover
      HeytingLean.Quantum.Contextuality.Triangle.model
      (fun {C} hC => HeytingLean.Quantum.Contextuality.Triangle.coverSubX (C := C) hC) := by
  exact HeytingLean.Quantum.Contextuality.Triangle.noGlobal

/-- Canonical obstruction class for the triangle witness. -/
def triangleObstructionClass : CechObstructionClass :=
  CechObstructionClass.h1_global_section

@[simp] theorem triangleObstructionClass_eq :
    triangleObstructionClass = CechObstructionClass.h1_global_section := rfl

theorem triangle_obstructionDegree :
    cohomologyDegree triangleObstructionClass = 1 := by
  rfl

theorem triangle_cech_profile :
    LocallyAdmissibleOnCover HeytingLean.Quantum.Contextuality.Triangle.model ∧
      HasCechH1
        HeytingLean.Quantum.Contextuality.Triangle.X
        HeytingLean.Quantum.Contextuality.Triangle.cover
        HeytingLean.Quantum.Contextuality.Triangle.model
        (fun {C} hC => HeytingLean.Quantum.Contextuality.Triangle.coverSubX (C := C) hC) := by
  exact ⟨locallyAdmissible_of_empirical _, triangle_has_cech_h1⟩

end ContextualityEngine

end PerspectivalPlenum
end HeytingLean
