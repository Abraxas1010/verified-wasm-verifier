import Mathlib.Order.Nucleus
import Mathlib.Order.Sublocale
import Mathlib.Tactic

/-!
# TWA ↔ Nucleus connection (Phase 1.5)

This module formalizes the **order-theoretic / logic-stabilizer** part of the "Quantum on a Laptop"
plan:

- given a nucleus `R`, define the **code space** as the fixed points `{x | R x = x}` (equivalently
  the image of `R`);
- show closure facts that are *provable now* (meet-closure, implication-closure into a closed
  target, etc.);
- provide a clean interface for "generators preserve the code space" via commutation with `R`;
- provide a `GaugeInvariantProjection` wrapper that lets stabilized observables descend to quotients
  without introducing global axioms.

Deep physics statements (gauge invariance of a particular model, triple-intersection → CCZ) are
represented as **structure fields** (assumptions), not global declarations.
-/

namespace HeytingLean
namespace Quantum
namespace TWA

universe u v

/-! ## Fixed points / code space for a nucleus -/

section FixedPoints

variable {Ω : Type u} [SemilatticeInf Ω]

/-- Fixed points of a nucleus as a set. -/
def codeSpaceSet (R : Nucleus Ω) : Set Ω := {x | R x = x}

@[simp] lemma mem_codeSpaceSet {R : Nucleus Ω} {x : Ω} : x ∈ codeSpaceSet R ↔ R x = x := Iff.rfl

lemma fixed_iff_exists_image (R : Nucleus Ω) (x : Ω) :
    R x = x ↔ ∃ y : Ω, R y = x := by
  constructor
  · intro hx
    exact ⟨x, hx⟩
  · rintro ⟨y, rfl⟩
    simp

lemma codeSpaceSet_inf_closed (R : Nucleus Ω) {x y : Ω}
    (hx : x ∈ codeSpaceSet R) (hy : y ∈ codeSpaceSet R) :
    x ⊓ y ∈ codeSpaceSet R := by
  -- `map_inf` gives `R (x ⊓ y) = R x ⊓ R y`.
  -- Rewrite the fixed-point hypotheses and finish.
  simp [codeSpaceSet] at hx hy
  simp [codeSpaceSet, hx, hy]

end FixedPoints

section FrameFixedPoints

variable {Ω : Type u} [Order.Frame Ω]

/-- Membership in the sublocale induced by a nucleus is equivalent to being a fixed point. -/
theorem mem_toSublocale_iff_fixed (R : Nucleus Ω) (x : Ω) :
    x ∈ R.toSublocale ↔ R x = x := by
  constructor
  · intro hx
    rcases (R.mem_toSublocale).1 hx with ⟨y, hy⟩
    -- `x = R y`, so `R x = R (R y) = R y = x`.
    calc
      R x = R (R y) := by simp [hy]
      _ = R y := R.idempotent y
      _ = x := hy
  · intro hx
    -- If `R x = x`, then `x` is in the image of `R` (choose `y := x`).
    exact (R.mem_toSublocale).2 ⟨x, hx⟩

/-- If the right side is closed, then `x ⇨ y` is closed. -/
lemma himp_fixed_of_fixed_right (R : Nucleus Ω) (x y : Ω) (hy : R y = y) :
    R (x ⇨ y) = x ⇨ y := by
  have hle : R (x ⇨ y) ≤ x ⇨ y := by
    simpa [hy] using (R.map_himp_le (x := x) (y := y))
  have hge : x ⇨ y ≤ R (x ⇨ y) :=
    Nucleus.le_apply (n := R) (x := x ⇨ y)
  exact le_antisymm hle hge

end FrameFixedPoints

/-! ## Stabilizer-style interface: generators commute with `R` -/

section Generators

variable {Ω : Type u} [SemilatticeInf Ω]

structure StabilizerCondition (Ω : Type u) [SemilatticeInf Ω] where
  R : Nucleus Ω
  Gen : Type v
  act : Gen → Ω → Ω
  /-- Commutation law: stabilizing after acting equals acting after stabilizing. -/
  commute : ∀ (g : Gen) (x : Ω), R (act g x) = act g (R x)

namespace StabilizerCondition

variable (S : StabilizerCondition Ω)

def codeSpace : Set Ω := codeSpaceSet S.R

@[simp] lemma mem_codeSpace {x : Ω} : x ∈ S.codeSpace ↔ S.R x = x := Iff.rfl

lemma act_preserves_fixed (g : S.Gen) {x : Ω} (hx : S.R x = x) :
    S.R (S.act g x) = S.act g x := by
  simpa [hx] using S.commute g x

/-- The code space as a subtype (elements fixed by `R`). -/
abbrev CodeSpaceType : Type u := {x : Ω // S.R x = x}

/-- Restrict generator action to the code space. -/
def actOnCodeSpace (g : S.Gen) : S.CodeSpaceType → S.CodeSpaceType :=
  fun x => ⟨S.act g x.1, S.act_preserves_fixed g x.2⟩

@[simp] lemma actOnCodeSpace_val (g : S.Gen) (x : S.CodeSpaceType) :
    (S.actOnCodeSpace g x).1 = S.act g x.1 := rfl

end StabilizerCondition

end Generators

/-! ## Gauge invariance as a quotient-friendly interface (no axioms) -/

section Gauge

variable {X : Type u} {Ω : Type v} [SemilatticeInf Ω]

/-- Package:
- a nucleus `R` on observables `Ω`,
- a projection `proj : X → Ω`,
- a gauge relation on `X`,
- and the single invariance assumption needed for well-defined stabilized observables on the quotient.
-/
structure GaugeInvariantProjection (X : Type u) (Ω : Type v) [SemilatticeInf Ω] where
  R : Nucleus Ω
  proj : X → Ω
  gauge : Setoid X
  stabilized_eq_of_gauge : ∀ ⦃x y : X⦄, gauge.r x y → R (proj x) = R (proj y)

namespace GaugeInvariantProjection

variable (G : GaugeInvariantProjection X Ω)

/-- The stabilized observable descends to the gauge quotient. -/
def stabilizedOnQuot : Quotient G.gauge → Ω :=
  Quotient.lift (fun x => G.R (G.proj x))
    (by
      intro x y hxy
      exact G.stabilized_eq_of_gauge hxy)

@[simp] lemma stabilizedOnQuot_mk (x : X) :
    G.stabilizedOnQuot (Quotient.mk G.gauge x) = G.R (G.proj x) := rfl

end GaugeInvariantProjection

end Gauge

/-! ## Topological CCZ note

The Phase 7 statement-level packaging for “triple intersection induces CCZ” now lives in
`HeytingLean.Quantum.TopologicalCCZ`.
-/

end TWA
end Quantum
end HeytingLean
