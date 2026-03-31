import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Topological CCZ via triple intersection (Phase 7, statement-level)

This module isolates the “**triple intersection induces CCZ**” claim behind a clean interface,
without importing any 3-manifold / cohomology / code-lattice machinery.

What we *do* implement (laptop-scale, fully provable):

* A minimal 3-qubit state model as an amplitude function `Ket 𝕜 := (Fin 2 × Fin 2 × Fin 2) → 𝕜`.
* The **CCZ** diagonal action on computational basis amplitudes (flip the sign of `|111⟩`).
* A parity-parameterized family `cczLike p` where `p : ZMod 2` toggles between identity (`p=0`)
  and CCZ (`p=1`).

What we *do not* prove here (and should remain an explicit assumption):

* Any topological theorem that identifies a physical “membrane intersection” invariant with the
  above `cczLike` action.

That topological content is represented as a structure field in `CCZFromTripleIntersection`.
-/

namespace HeytingLean
namespace Quantum

namespace TopologicalCCZ

universe u v w

/-! ## A tiny 3-qubit amplitude model -/

/-- A bit, used for computational basis indices. -/
abbrev Bit : Type := Fin 2

/-- Computational basis index for 3 qubits. -/
abbrev Q3 : Type := Bit × Bit × Bit

/-- A “ket” as an amplitude function on computational basis indices. -/
abbrev Ket (𝕜 : Type w) : Type w := Q3 → 𝕜

/-- The `|111⟩` basis index. -/
def ket111 : Q3 := (1, 1, 1)

/-! ## CCZ as a sign flip on `|111⟩` -/

/-- A parity-parameterized CCZ-like diagonal action:

* if `p = 0`, this is the identity;
* if `p ≠ 0` (equivalently `p = 1` in `ZMod 2`), flip the sign of the `|111⟩` amplitude.
-/
def cczLike {𝕜 : Type w} [AddGroup 𝕜] (p : ZMod 2) (ψ : Ket 𝕜) : Ket 𝕜 :=
  fun q =>
    if q = ket111 then
      if p = 0 then ψ q else -ψ q
    else ψ q

/-- The CCZ gate (the `p = 1` case of `cczLike`). -/
def CCZ {𝕜 : Type w} [AddGroup 𝕜] : Ket 𝕜 → Ket 𝕜 :=
  cczLike (𝕜 := 𝕜) (p := (1 : ZMod 2))

namespace cczLikeLemmas

variable {𝕜 : Type w} [AddGroup 𝕜]

@[simp] lemma apply_of_ne_111 (p : ZMod 2) (ψ : Ket 𝕜) (q : Q3) (hq : q ≠ ket111) :
    TopologicalCCZ.cczLike (𝕜 := 𝕜) p ψ q = ψ q := by
  simp [TopologicalCCZ.cczLike, hq]

@[simp] lemma apply_111_of_eq_zero (ψ : Ket 𝕜) :
    TopologicalCCZ.cczLike (𝕜 := 𝕜) (0 : ZMod 2) ψ ket111 = ψ ket111 := by
  simp [TopologicalCCZ.cczLike, ket111]

@[simp] lemma apply_111_of_ne_zero (p : ZMod 2) (ψ : Ket 𝕜) (hp : p ≠ 0) :
    TopologicalCCZ.cczLike (𝕜 := 𝕜) p ψ ket111 = -ψ ket111 := by
  simp [TopologicalCCZ.cczLike, ket111, hp]

@[simp] lemma eq_self_of_eq_zero (ψ : Ket 𝕜) :
    TopologicalCCZ.cczLike (𝕜 := 𝕜) (0 : ZMod 2) ψ = ψ := by
  funext q
  by_cases hq : q = ket111
  · subst hq
    simp [TopologicalCCZ.cczLike, ket111]
  · simp [TopologicalCCZ.cczLike, hq]

@[simp] lemma involutive (p : ZMod 2) :
    Function.Involutive (TopologicalCCZ.cczLike (𝕜 := 𝕜) p) := by
  intro ψ
  funext q
  by_cases hq : q = ket111
  · subst hq
    by_cases hp : p = 0
    · simp [TopologicalCCZ.cczLike, ket111, hp]
    · simp [TopologicalCCZ.cczLike, ket111, hp]
  · simp [TopologicalCCZ.cczLike, hq]

end cczLikeLemmas

namespace CCZ

variable {𝕜 : Type w} [AddGroup 𝕜]

@[simp] lemma apply_of_ne_111 (ψ : Ket 𝕜) (q : Q3) (hq : q ≠ ket111) :
    CCZ (𝕜 := 𝕜) ψ q = ψ q := by
  simp [CCZ, cczLikeLemmas.apply_of_ne_111 (𝕜 := 𝕜) (p := (1 : ZMod 2)) ψ q hq]

@[simp] lemma apply_111 (ψ : Ket 𝕜) :
    CCZ (𝕜 := 𝕜) ψ ket111 = -ψ ket111 := by
  -- In `ZMod 2`, `1 ≠ 0`.
  have h1 : (1 : ZMod 2) ≠ 0 := by decide
  simp [CCZ, cczLikeLemmas.apply_111_of_ne_zero (𝕜 := 𝕜) (p := (1 : ZMod 2)) ψ h1]

@[simp] lemma involutive : Function.Involutive (CCZ (𝕜 := 𝕜)) := by
  simp [CCZ, cczLikeLemmas.involutive (𝕜 := 𝕜) (p := (1 : ZMod 2))]

end CCZ

/-! ## Triple intersection interface (parity only) -/

/-- A topological triple-intersection oracle, returning parity in `ZMod 2`. -/
structure TripleIntersectionModel (T : Type u) where
  /-- Type of the objects whose triple intersection is measured (e.g. membranes / cycles). -/
  Cycle : Type v
  /-- Triple intersection parity. -/
  triple : Cycle → Cycle → Cycle → ZMod 2

/-- Statement-only packaging: a physical gate is assumed to be governed by a triple intersection
parity, yielding a `cczLike` action on 3-qubit amplitudes.

No topology is proved here: the key link is the field `gate_spec`. -/
structure CCZFromTripleIntersection (T : Type u) (𝕜 : Type w) [AddGroup 𝕜] where
  topo : TripleIntersectionModel (T := T)
  /-- Three distinguished cycles corresponding to the three logical qubits. -/
  membrane : Fin 3 → topo.Cycle
  /-- The physical action on 3-qubit amplitudes. -/
  topoGate : Ket 𝕜 → Ket 𝕜
  /-- The imported theorem boundary: the action is exactly `cczLike` with parity given by the
  triple intersection of the three membranes. -/
  gate_spec :
    ∀ ψ q,
      topoGate ψ q =
        cczLike (𝕜 := 𝕜) (topo.triple (membrane 0) (membrane 1) (membrane 2)) ψ q

namespace CCZFromTripleIntersection

variable {T : Type u} {𝕜 : Type w} [AddGroup 𝕜]
  (S : CCZFromTripleIntersection (T := T) (𝕜 := 𝕜))

/-- The triple intersection parity that controls the CCZ-like phase. -/
def parity : ZMod 2 :=
  S.topo.triple (S.membrane 0) (S.membrane 1) (S.membrane 2)

lemma topoGate_eq_cczLike : S.topoGate = cczLike (𝕜 := 𝕜) S.parity := by
  funext ψ q
  simp [parity, S.gate_spec]

lemma topoGate_eq_id_of_parity_zero (h : S.parity = 0) : S.topoGate = id := by
  have hGate : S.topoGate = cczLike (𝕜 := 𝕜) S.parity := S.topoGate_eq_cczLike
  calc
    S.topoGate = cczLike (𝕜 := 𝕜) S.parity := hGate
    _ = cczLike (𝕜 := 𝕜) (0 : ZMod 2) := by simp [h]
    _ = id := by
      funext ψ
      simp [cczLikeLemmas.eq_self_of_eq_zero (𝕜 := 𝕜) ψ]

lemma topoGate_eq_CCZ_of_parity_one (h : S.parity = 1) : S.topoGate = CCZ (𝕜 := 𝕜) := by
  have : S.topoGate = cczLike (𝕜 := 𝕜) S.parity := S.topoGate_eq_cczLike
  -- `CCZ` is `cczLike 1`.
  simp [CCZ, this, h]

end CCZFromTripleIntersection

end TopologicalCCZ

end Quantum
end HeytingLean
