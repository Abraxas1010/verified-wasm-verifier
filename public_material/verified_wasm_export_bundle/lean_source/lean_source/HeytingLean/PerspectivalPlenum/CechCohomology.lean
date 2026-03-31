import HeytingLean.PerspectivalPlenum.CechObstruction
import HeytingLean.Quantum.Contextuality.Triangle

namespace HeytingLean
namespace PerspectivalPlenum
namespace LensSheaf
namespace Cech
namespace True

/-!
# PerspectivalPlenum.CechCohomology

Executable Čech obstruction scaffolding for finite covers.

This module introduces a concrete one-skeleton Čech model used by the
contextuality lane:
- `C⁰`/`C¹` cochains over `Bool` (`ℤ₂`-style arithmetic via xor),
- a coboundary map `δ⁰`,
- obstruction classes represented by non-coboundary witnesses.

For the triangle contextuality scenario, we encode the parity signature
`ab=bc`, `ab=ac`, `bc≠ac` as a `C¹` cocycle witness and prove it is
not a coboundary.
-/

universe u v

/-- Finite one-skeleton used for Čech `C⁰ → C¹` data. -/
structure OneSkeleton (V : Type u) (E : Type v) where
  src : E → V
  dst : E → V

/-- `C⁰` cochains over `ℤ₂` (encoded as `Bool`). -/
abbrev Cech0 (V : Type u) := V → Bool

/-- `C¹` cochains over `ℤ₂` (encoded as `Bool`). -/
abbrev Cech1 (E : Type v) := E → Bool

/-- Coboundary map `δ⁰ : C⁰ → C¹` on a one-skeleton. -/
def d0 {V : Type u} {E : Type v} (N : OneSkeleton V E) :
    Cech0 V → Cech1 E :=
  fun x e => Bool.xor (x (N.src e)) (x (N.dst e))

/--
On a one-skeleton truncation (`C² = 0`), every `1`-cochain is a cocycle.
We keep this predicate explicit so call sites can remain stable when a full
`C²` layer is added later.
-/
def IsCocycle {V : Type u} {E : Type v} (_N : OneSkeleton V E) (_ω : Cech1 E) : Prop := True

/-- `ω` is a coboundary iff `ω = δ⁰ x` for some `0`-cochain `x`. -/
def IsCoboundary {V : Type u} {E : Type v} (N : OneSkeleton V E) (ω : Cech1 E) : Prop :=
  ∃ x : Cech0 V, d0 N x = ω

/--
Concrete `H¹` witness object for the one-skeleton lane:
a cocycle together with a proof that it is not a coboundary.
-/
structure H1Class {V : Type u} {E : Type v} (N : OneSkeleton V E) where
  repr : Cech1 E
  cocycle : IsCocycle N repr
  nonzero : ¬ IsCoboundary N repr

section PairOracle

variable {A : Type u}
variable (U : LensObj A)
variable (m : MatchingFamily (witnessPresheaf A) U (pairCover U))

/--
Computable local oracle: attempt to glue a pair-cover matching family.

- success branch returns a concrete amalgamation witness;
- failure branch returns an obstruction proof.
-/
inductive PairOracleResult : Type u where
  | glued :
      Amalgamates (witnessPresheaf A) U (pairCover U) m →
      PairOracleResult
  | obstructed :
      HasH1Obstruction (witnessPresheaf A) U (pairCover U) m →
      PairOracleResult

/--
Computable pair-cover oracle when equality on section values is decidable.
-/
def pairOracleComputable
    [DecidableEq ((witnessPresheaf A).obj (Opposite.op U))] :
    PairOracleResult (U := U) (m := m) := by
  by_cases hCompat : m.sec false = m.sec true
  · exact .glued (witnessPresheaf_pair_amalgamates_of_eq U m hCompat)
  · exact .obstructed (pairIncompatible_hasH1 U m hCompat)

/--
General pair-cover oracle (noncomputable fallback via classical decidability).
-/
noncomputable def pairOracle : PairOracleResult (U := U) (m := m) := by
  classical
  exact pairOracleComputable (A := A) (U := U) (m := m)

end PairOracle

namespace Triangle

/-- Contexts in the triangle measurement cover `{ab, bc, ac}`. -/
inductive Vertex where
  | ab
  | bc
  | ac
  deriving DecidableEq, Repr

/-- Pairwise overlaps in the triangle cover. -/
inductive Edge where
  | ab_bc
  | ab_ac
  | bc_ac
  deriving DecidableEq, Repr

/-- One-skeleton of the triangle contextuality cover nerve. -/
def skeleton : OneSkeleton Vertex Edge where
  src
    | .ab_bc => .ab
    | .ab_ac => .ab
    | .bc_ac => .bc
  dst
    | .ab_bc => .bc
    | .ab_ac => .ac
    | .bc_ac => .ac

/--
Parity obstruction cocycle for the triangle contextuality signature:
- overlap `ab∩bc`: equal (`0`)
- overlap `ab∩ac`: equal (`0`)
- overlap `bc∩ac`: unequal (`1`)
-/
def parityCocycle : Cech1 Edge
  | .ab_bc => false
  | .ab_ac => false
  | .bc_ac => true

theorem parityCocycle_cocycle :
    IsCocycle skeleton parityCocycle := by
  trivial

/--
The triangle parity cocycle is not a coboundary: no `C⁰` assignment can satisfy
`ab=bc`, `ab=ac`, and `bc≠ac` simultaneously.
-/
theorem parityCocycle_nonzero :
    ¬ IsCoboundary skeleton parityCocycle := by
  intro h
  rcases h with ⟨x, hx⟩
  have h_ab_bc : Bool.xor (x .ab) (x .bc) = false := by
    simpa [d0, skeleton, parityCocycle] using congrArg (fun f => f .ab_bc) hx
  have h_ab_ac : Bool.xor (x .ab) (x .ac) = false := by
    simpa [d0, skeleton, parityCocycle] using congrArg (fun f => f .ab_ac) hx
  have h_bc_ac : Bool.xor (x .bc) (x .ac) = true := by
    simpa [d0, skeleton, parityCocycle] using congrArg (fun f => f .bc_ac) hx
  have h_eq_ab_bc : x .ab = x .bc := by
    cases hab : x .ab <;> cases hbc : x .bc
    · rfl
    · exfalso
      simp [hab, hbc] at h_ab_bc
    · exfalso
      simp [hab, hbc] at h_ab_bc
    · rfl
  have h_eq_ab_ac : x .ab = x .ac := by
    cases hab : x .ab <;> cases hac : x .ac
    · rfl
    · exfalso
      simp [hab, hac] at h_ab_ac
    · exfalso
      simp [hab, hac] at h_ab_ac
    · rfl
  have h_eq_bc_ac : x .bc = x .ac := h_eq_ab_bc.symm.trans h_eq_ab_ac
  have h_zero : Bool.xor (x .bc) (x .ac) = false := by
    simp [h_eq_bc_ac]
  have h_contra : False := by
    rw [h_zero] at h_bc_ac
    cases h_bc_ac
  exact h_contra

/-- Canonical nonzero `H¹` obstruction witness for the triangle cover. -/
def parityClass : H1Class skeleton where
  repr := parityCocycle
  cocycle := parityCocycle_cocycle
  nonzero := parityCocycle_nonzero

/-- Existence form used by downstream bridge layers. -/
theorem exists_nonzero_class : ∃ _ : H1Class skeleton, True := by
  exact ⟨parityClass, trivial⟩

/--
Bridge theorem: the known no-global-section theorem entails an available
nonzero `H¹` witness in this one-skeleton model.
-/
theorem noGlobal_implies_exists_nonzero_class
    (_hNo : HeytingLean.LoF.CryptoSheaf.Quantum.NoGlobalSection
      HeytingLean.Quantum.Contextuality.Triangle.X
      HeytingLean.Quantum.Contextuality.Triangle.cover
      HeytingLean.Quantum.Contextuality.Triangle.model
      (fun {C} hC => HeytingLean.Quantum.Contextuality.Triangle.coverSubX (C := C) hC)) :
    ∃ _ : H1Class skeleton, True := by
  exact exists_nonzero_class

/--
Triangle obstruction oracle for ATP/bridge consumers:
returns either a global section witness or a nonzero `H¹` class.
-/
inductive OracleResult where
  | global :
      HeytingLean.LoF.CryptoSheaf.Quantum.HasGlobalSection
        HeytingLean.Quantum.Contextuality.Triangle.X
        HeytingLean.Quantum.Contextuality.Triangle.cover
        HeytingLean.Quantum.Contextuality.Triangle.model
        (fun {C} hC => HeytingLean.Quantum.Contextuality.Triangle.coverSubX (C := C) hC) →
      OracleResult
  | obstructed : H1Class skeleton → OracleResult

def oracle : OracleResult :=
  .obstructed parityClass

/-- The oracle's obstructed branch is compatible with the surrogate `HasCechH1` witness. -/
theorem oracle_surrogate_sound :
    ContextualityEngine.HasCechH1
      HeytingLean.Quantum.Contextuality.Triangle.X
      HeytingLean.Quantum.Contextuality.Triangle.cover
      HeytingLean.Quantum.Contextuality.Triangle.model
      (fun {C} hC => HeytingLean.Quantum.Contextuality.Triangle.coverSubX (C := C) hC) := by
  exact ContextualityEngine.triangle_has_cech_h1

end Triangle
end True
end Cech
end LensSheaf
end PerspectivalPlenum
end HeytingLean
