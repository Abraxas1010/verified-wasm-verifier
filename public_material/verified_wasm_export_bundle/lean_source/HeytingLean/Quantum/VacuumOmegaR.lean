import HeytingLean.Quantum.OML.Core
import HeytingLean.Quantum.Translate.Core
import HeytingLean.Quantum.Translate.Omega
import HeytingLean.Quantum.Translate.RT
import HeytingLean.Logic.PSR
import HeytingLean.Epistemic.Occam
import HeytingLean.LoF.Nucleus

/-
Blueprint scaffold for relating a “quantum vacuum” proposition in an
orthomodular lattice to the Ωᵣ fixed-point core of a reentry nucleus.

Phase 1: this file only sets up the abstract data and basic aliases; the
main equivalence theorem and concrete instances live in later phases.
-/

open scoped Classical

namespace HeytingLean
namespace Quantum

open HeytingLean.Quantum.OML
open HeytingLean.Quantum.Translate
open HeytingLean.LoF

/-! ## Vacuum witness on an orthomodular lattice -/

universe u v

variable {β : Type u}

/-- Abstract data for a “quantum vacuum” proposition inside an orthomodular
    lattice. The vacuum is assumed to be nontrivial; additional minimality
    properties can be added later if the equivalence proof requires them. -/
structure VacuumWitness (β : Type u)
  [OrthocomplementedLattice β] [OrthomodularLattice β] where
  /-- Distinguished proposition representing the vacuum state. -/
  vacuum : β
  /-- The vacuum is not bottom in the lattice. -/
  nontrivial : vacuum ≠ ⊥

/-! ## Reentry–modality bridge and Ω-core alignment -/

namespace Reentry

variable {α : Type v} [PrimaryAlgebra α]

/-- View a `LoF.Reentry` nucleus as a quantum translation modality on the
    same ambient carrier. This packages the nucleus together with the fact
    that it preserves `⊤` as required by `Quantum.Translate.Modality`. -/
def toQuantumModality (R : Reentry α) : Quantum.Translate.Modality α where
  J := R.nucleus
  preserves_top := by
    -- Nuclei preserve `⊤` on any complete lattice.
    have hle : (⊤ : α) ≤ R.nucleus ⊤ :=
      Nucleus.le_apply (n := R.nucleus) (x := ⊤)
    have htop : R.nucleus ⊤ ≤ (⊤ : α) := le_top
    exact le_antisymm htop hle

/-- Fixed-point carrier for the quantum modality induced by a reentry
    nucleus. This is definitionally the same as `R.Omega`. -/
abbrev OmegaQuantum (R : Reentry α) : Type v :=
  Quantum.Translate.Omega (M := toQuantumModality (R := R))

end Reentry

/-- Abstract context bundling the ingredients used by the vacuum–Ωᵣ
    blueprint: an orthomodular lattice of propositions `β`, an ambient
    complete lattice `α` with a reentry nucleus `R`, a translation `F`
    from `β` into `α`, and a distinguished vacuum proposition. -/
structure VacuumOmegaRContext
    (β : Type u) (α : Type v)
    [OrthocomplementedLattice β] [OrthomodularLattice β]
    [LoF.PrimaryAlgebra α] where
  (F : QLMap β α)
  (R : LoF.Reentry α)
  /-- Compatibility condition tying the quantum modality `F.M` to the
      reentry nucleus: they share the same underlying closure operator. -/
  modality_agrees : ∀ a : α, F.M.J a = R.nucleus a
  (vacuum : VacuumWitness β)
  /-- Bridge hypothesis: the Ω-core image of the vacuum coincides with the
      primordial fixed point of the reentry nucleus in the ambient algebra. -/
  vacuum_primordial :
    F.M.close (F.tr vacuum.vacuum) = R.primordial

namespace VacuumOmegaRContext

variable {β : Type u} {α : Type v}
variable [OrthocomplementedLattice β] [OrthomodularLattice β]
variable [LoF.PrimaryAlgebra α]

open HeytingLean.Logic
open HeytingLean.Logic.PSR
open HeytingLean.Epistemic

/-- Underlying vacuum proposition in the orthomodular lattice. -/
@[simp] def vacuumProp (C : VacuumOmegaRContext β α) : β :=
  C.vacuum.vacuum

@[simp] lemma vacuum_nontrivial (C : VacuumOmegaRContext β α) :
    C.vacuumProp ≠ (⊥ : β) :=
  C.vacuum.nontrivial

/-- Ambient Ω-level image of the vacuum under the quantum translation map,
    viewed in the fixed-point core for `C.F.M`. -/
def vacuumOmegaCore (C : VacuumOmegaRContext β α) :
    Quantum.Translate.Omega (M := C.F.M) :=
  (C.F).toOmega C.vacuumProp

/-- Underlying ambient element of the Ω-core vacuum. -/
@[simp] lemma vacuumOmegaCore_coe (C : VacuumOmegaRContext β α) :
    ((vacuumOmegaCore C : Quantum.Translate.Omega (M := C.F.M)) : α)
      = C.F.M.close (C.F.tr C.vacuumProp) :=
  by
    -- unfold through the `toOmega` helper and reuse its coercion lemma
    simp [vacuumOmegaCore,
      Quantum.Translate.QLMap.toOmega_coe]

/-- The Ω-core vacuum is a fixed point of the quantum modality `C.F.M`. -/
lemma vacuumOmegaCore_fixed (C : VacuumOmegaRContext β α) :
    C.F.M.J ((vacuumOmegaCore C : Quantum.Translate.Omega (M := C.F.M)) : α)
      = vacuumOmegaCore C :=
  Quantum.Translate.Omega.closed (M := C.F.M) (x := vacuumOmegaCore C)

/-- Ω-core image of an arbitrary vacuum witness under the quantum translation map. -/
def witnessOmegaCore (C : VacuumOmegaRContext β α) (v : VacuumWitness β) :
    Quantum.Translate.Omega (M := C.F.M) :=
  (C.F).toOmega v.vacuum

/-- Ωᴿ-level image of an arbitrary vacuum witness: we mirror the construction
used for `vacuumOmega`, but parameterised over the witness. -/
def witnessImage (C : VacuumOmegaRContext β α) (v : VacuumWitness β) :
    C.R.Omega := by
  -- First form the Ω-image for the quantum modality.
  let x : Quantum.Translate.Omega (M := C.F.M) := C.witnessOmegaCore v
  have hx_closed :
      C.F.M.J ((x : Quantum.Translate.Omega (M := C.F.M)) : α) = x :=
    Quantum.Translate.Omega.closed (M := C.F.M) (x := x)
  -- Transport the fixed-point property along the reentry/quantum-modality
  -- compatibility to view `x` as fixed by `C.R`.
  have hR' :
      C.R.nucleus ((x : Quantum.Translate.Omega (M := C.F.M)) : α) = x := by
    have hcompat := C.modality_agrees ((x : Quantum.Translate.Omega (M := C.F.M)) : α)
    calc
      C.R.nucleus ((x : Quantum.Translate.Omega (M := C.F.M)) : α)
          = C.F.M.J ((x : Quantum.Translate.Omega (M := C.F.M)) : α) := by
              simpa using hcompat.symm
      _ = x := hx_closed
  have hR :
      C.R ((x : Quantum.Translate.Omega (M := C.F.M)) : α) = x := by
    simpa [LoF.Reentry.coe_nucleus] using hR'
  -- Finally, package the ambient element as an Ωᴿ fixed point.
  exact LoF.Reentry.Omega.mk (R := C.R)
    ((x : Quantum.Translate.Omega (M := C.F.M)) : α) hR

/-- Underlying ambient element of the witness image in Ωᴿ. -/
@[simp] lemma witnessImage_coe (C : VacuumOmegaRContext β α)
    (v : VacuumWitness β) :
    ((C.witnessImage v : C.R.Omega) : α)
      = C.F.M.close (C.F.tr v.vacuum) := by
  unfold witnessImage witnessOmegaCore
  simp [Quantum.Translate.QLMap.toOmega_coe]

/-- Ωᴿ-level image of the vacuum: we take the Ω-core image under `C.F.M` and
    repackage it using the reentry nucleus `C.R`, relying on the compatibility
    `modality_agrees` to show it is also a fixed point of `C.R`. -/
def vacuumOmega (C : VacuumOmegaRContext β α) : C.R.Omega := by
  let x : Quantum.Translate.Omega (M := C.F.M) := vacuumOmegaCore C
  have hx_closed :
      C.F.M.J ((x : Quantum.Translate.Omega (M := C.F.M)) : α) = x :=
    Quantum.Translate.Omega.closed (M := C.F.M) (x := x)
  have hR' :
      C.R.nucleus ((x : Quantum.Translate.Omega (M := C.F.M)) : α) = x := by
    -- transport the fixed-point property along the nucleus compatibility
    have hcompat := C.modality_agrees ((x : Quantum.Translate.Omega (M := C.F.M)) : α)
    -- `hcompat : C.F.M.J _ = C.R.nucleus _`
    calc
      C.R.nucleus ((x : Quantum.Translate.Omega (M := C.F.M)) : α)
          = C.F.M.J ((x : Quantum.Translate.Omega (M := C.F.M)) : α) := by
              simpa using hcompat.symm
      _ = x := hx_closed
  -- rewrite to view the equality in terms of `C.R` as a function
  have hR :
      C.R ((x : Quantum.Translate.Omega (M := C.F.M)) : α) = x := by
    simpa [LoF.Reentry.coe_nucleus] using hR'
  exact LoF.Reentry.Omega.mk (R := C.R)
    ((x : Quantum.Translate.Omega (M := C.F.M)) : α) hR

/-- Underlying ambient element of the Ωᴿ-level vacuum image. -/
@[simp] lemma vacuumOmega_coe (C : VacuumOmegaRContext β α) :
    ((C.vacuumOmega : C.R.Omega) : α)
      = C.F.M.close (C.F.tr C.vacuumProp) := by
  -- by construction, `vacuumOmega` is built from the same ambient element as
  -- `vacuumOmegaCore`.
  -- simplify through the constructors on both Ω-cores.
  simp [vacuumOmega, vacuumOmegaCore]

/-- The distinguished `vacuumOmega` coincides with the Ωᴿ image of its own
vacuum witness. This is just a rephrasing of the construction of
`vacuumOmega` in terms of the general `witnessImage` helper. -/
lemma vacuumOmega_eq_witnessImage (C : VacuumOmegaRContext β α) :
    C.vacuumOmega = C.witnessImage C.vacuum := by
  ext : 1
  -- Compare ambient carriers; both are built from the same closed image.
  simp [vacuumOmega_coe, witnessImage_coe, vacuumProp]

/-- In the abstract blueprint context, the Ωᴿ-level vacuum image coincides
    with the primordial fixed point packaged by the reentry nucleus. -/
lemma vacuumOmega_eq_process (C : VacuumOmegaRContext β α) :
    C.vacuumOmega = C.R.process := by
  ext : 1
  -- compare ambient carriers using the bridge hypothesis
  simpa [vacuumOmega_coe, LoF.Reentry.process_coe, vacuumProp] using
    C.vacuum_primordial

/-- Consequently, the Ωᴿ-level vacuum equals the Euler boundary (recursive
    zero) in the LoF fixed-point core. -/
theorem vacuumOmega_eq_eulerBoundary (C : VacuumOmegaRContext β α) :
    C.vacuumOmega = C.R.eulerBoundary := by
  -- `eulerBoundary` is definitionally equal to the primordial process.
  simpa [LoF.Reentry.eulerBoundary_eq_process] using C.vacuumOmega_eq_process

/-- The vacuum fixed point is strictly positive in the ambient algebra and
    thus a boundary candidate. -/
lemma vacuumOmega_pos (C : VacuumOmegaRContext β α) :
    ⊥ < ((C.vacuumOmega : C.R.Omega) : α) := by
  -- transfer positivity from the primordial process.
  have := LoF.Reentry.process_pos (R := C.R)
  -- coerce both sides via the coincidence lemma.
  simpa [C.vacuumOmega_eq_process] using this

lemma vacuumOmega_mem_boundaryCandidates (C : VacuumOmegaRContext β α) :
    C.vacuumOmega ∈ C.R.boundaryCandidates := by
  -- Transport the generic process-level candidate lemma along the
  -- coincidence `vacuumOmega_eq_process`.
  have h := LoF.Reentry.process_mem_boundaryCandidates (R := C.R)
  simpa [C.vacuumOmega_eq_process] using h

/-- PSR view: the Ωᴿ-level vacuum image is a sufficient reason in the
    sense of the LoF `PSR` kernel (fixed by the reentry nucleus). -/
lemma vacuumOmega_psr (C : VacuumOmegaRContext β α) :
    PSR.Sufficient (R := C.R)
      (((C.vacuumOmega : C.R.Omega) : α)) := by
  -- `apply_coe` witnesses fixedness at the Ωᴿ level; repackage it for PSR.
  have h :=
    LoF.Reentry.Omega.apply_coe (R := C.R) (a := C.vacuumOmega)
  -- coerce the right-hand side to live in `α`.
  have h' :
      C.R (((C.vacuumOmega : C.R.Omega) : α)) =
        ((C.vacuumOmega : C.R.Omega) : α) := by
    simpa using h
  exact PSR.sufficient_of_fixed (R := C.R)
    (a := ((C.vacuumOmega : C.R.Omega) : α)) h'

/-- Occam / recursive-zero view: the Ωᴿ-level vacuum has birthday zero in
    the iterated-nucleus sense, because it coincides with the Euler boundary. -/
lemma vacuumOmega_birth_zero (C : VacuumOmegaRContext β α) :
    birth C.R (((C.vacuumOmega : C.R.Omega) : α)) = 0 := by
  -- reuse the generic Euler-boundary birthday lemma.
  -- `birth C.R ((C.R.eulerBoundary : C.R.Omega) : α) = 0`
  simp [C.vacuumOmega_eq_eulerBoundary]

/-- Any vacuum witness whose image under the translation/closure pipeline
lands on the primordial element induces the Euler boundary in Ωᴿ. -/
lemma witnessImage_eq_eulerBoundary (C : VacuumOmegaRContext β α)
    (v : VacuumWitness β)
    (h : C.F.M.close (C.F.tr v.vacuum) = C.R.primordial) :
    C.witnessImage v = C.R.eulerBoundary := by
  ext : 1
  -- Compare ambient carriers using the given bridge hypothesis and the
  -- definitional properties of `process` and `eulerBoundary`.
  have hw :
      ((C.witnessImage v : C.R.Omega) : α) = C.R.primordial := by
    simpa [witnessImage_coe] using h
  have hb :
      ((C.R.eulerBoundary : C.R.Omega) : α) = C.R.primordial := by
    simp [LoF.Reentry.eulerBoundary_eq_process, LoF.Reentry.process_coe]
  -- Rewrite both sides through `C.R.primordial`.
  calc
    ((C.witnessImage v : C.R.Omega) : α)
        = C.R.primordial := hw
    _ = ((C.R.eulerBoundary : C.R.Omega) : α) := hb.symm

/-- Order-theoretic uniqueness: among Ωᴿ fixed points that are strictly
above `⊥`, lie inside the designated support window, and are pointwise
below every other such positive fixed point, the vacuum coincides with
`C.vacuumOmega` (and hence with the Euler boundary). -/
lemma vacuumOmega_unique_minimal (C : VacuumOmegaRContext β α)
    (x : C.R.Omega)
    (hx_nontrivial : ⊥ < (x : α))
    (hx_support : (x : α) ≤ C.R.support)
    (hx_min : ∀ y : C.R.Omega, ⊥ < (y : α) → (x : α) ≤ (y : α)) :
    x = C.vacuumOmega := by
  -- First identify `x` with the Euler boundary using the generic LoF lemma.
  have hx_eq_euler :
      x = C.R.eulerBoundary :=
    LoF.Reentry.eulerBoundary_unique_minimal (R := C.R)
      (x := x) hx_nontrivial hx_support hx_min
  -- Then transport along the coincidence of `vacuumOmega` and Euler boundary.
  simpa [C.vacuumOmega_eq_eulerBoundary] using hx_eq_euler

/-- Support-aware variant of `vacuumOmega_unique_minimal`: it is enough to
assume minimality of `x` only with respect to positive Ωᴿ fixed points that
lie inside the designated support window. -/
lemma vacuumOmega_unique_minimal_support (C : VacuumOmegaRContext β α)
    (x : C.R.Omega)
    (hx_nontrivial : ⊥ < (x : α))
    (hx_support : (x : α) ≤ C.R.support)
    (hx_min :
      ∀ y : C.R.Omega, ⊥ < (y : α) → (y : α) ≤ C.R.support →
        (x : α) ≤ (y : α)) :
    x = C.vacuumOmega := by
  have hx_eq_euler :
      x = C.R.eulerBoundary :=
    LoF.Reentry.eulerBoundary_unique_minimal_support (R := C.R)
      (x := x) hx_nontrivial hx_support hx_min
  simpa [C.vacuumOmega_eq_eulerBoundary] using hx_eq_euler

/-- Any two vacuum witnesses whose translation/closure images both coincide
with the primordial element induce the same Ωᴿ fixed point. In particular,
their Ωᴿ “vacuum images” are equal. -/
lemma vacuum_image_unique (C : VacuumOmegaRContext β α)
    (v₁ v₂ : VacuumWitness β)
    (h₁ : C.F.M.close (C.F.tr v₁.vacuum) = C.R.primordial)
    (h₂ : C.F.M.close (C.F.tr v₂.vacuum) = C.R.primordial) :
    C.witnessImage v₁ = C.witnessImage v₂ := by
  -- Both witness images coincide with the Euler boundary by
  -- `witnessImage_eq_eulerBoundary`.
  have h₁' := C.witnessImage_eq_eulerBoundary v₁ h₁
  have h₂' := C.witnessImage_eq_eulerBoundary v₂ h₂
  simp [h₁', h₂']

end VacuumOmegaRContext

end Quantum
end HeytingLean
