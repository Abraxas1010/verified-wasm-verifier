import HeytingLean.Quantum.OML.Examples.QGIInterferometer
import HeytingLean.Quantum.EnergyObservable
import HeytingLean.Quantum.QGIContext

/-
Finite QGI energy observable on the four-element OML `QGIβ`.

This module provides a minimal `EnergyObservable QGIβ` witnessing the
idea that:

* the `labPath` proposition is the zero-energy (vacuum) eigenspace;
* `freePath` is a simple excited energy level; and
* all other energies map to bottom.

It is intended as a conceptual example; it is not used by the core
vacuum/Ωᴿ equivalence proofs.
-/

namespace HeytingLean
namespace Quantum
namespace QGI

open HeytingLean.Quantum.OML.QGIInterferometer
open HeytingLean.Quantum.OML
open HeytingLean.Quantum

/-- A symbolic two-level energy observable on the QGI OML carrier
`QGIβ := H2`:

* `E = 0` maps to `labPath` (vacuum/ground state);
* `E = 1` maps to `freePath` (excited state);
* all other energies map to `⊥`. -/
noncomputable def energyDemo : EnergyObservable QGIβ := by
  classical
  -- Local abbreviation for the eigenspace family.
  let f : ℝ → QGIβ := fun E =>
    if E = 0 then labPath
    else if E = 1 then freePath
    else ⊥
  refine
    { eigenspaces := f
      eigenspaces_ortho := ?_
      eigenspaces_complete := ?_ }
  · -- Orthogonality of distinct eigenspaces.
    intro E₁ E₂ hneq
    classical
    -- Case 1: `E₁ = 0`.
    by_cases hE₁0 : E₁ = 0
    · subst hE₁0
      have hE₂ne0 : E₂ ≠ 0 := by
        intro h
        exact hneq (by simpa [h] : (0 : ℝ) = E₂)
      by_cases hE₂1 : E₂ = 1
      · -- Eigenspaces at 0 and 1 are `labPath` and `freePath`.
        -- Their meet is bottom in the QGI lattice.
        have : f 0 ⊓ f 1 = (⊥ : QGIβ) := by
          simp [f, QGIInterferometer.inf_lab_free]
        simpa [f, hE₂1] using this
      · -- All other energies map to bottom.
        have : f 0 ⊓ f E₂ = (⊥ : QGIβ) := by
          simp [f, hE₂ne0, hE₂1]
        exact this
    · -- Case 2: `E₁ ≠ 0`.
      by_cases hE₁1 : E₁ = 1
      · -- Subcase 2a: `E₁ = 1`.
        subst hE₁1
        have hE₂ne1 : E₂ ≠ 1 := by
          intro h
          exact hneq (by simpa [h] : (1 : ℝ) = E₂)
        by_cases hE₂0 : E₂ = 0
        · -- Eigenspaces at 1 and 0 are `freePath` and `labPath`.
          have : f 1 ⊓ f 0 = (⊥ : QGIβ) := by
            simp [f, QGIInterferometer.inf_free_lab]
          simpa [f, hE₂0] using this
        · -- All other energies map to bottom.
          have : f 1 ⊓ f E₂ = (⊥ : QGIβ) := by
            simp [f, hE₂0, hE₂ne1]
          exact this
      · -- Subcase 2b: `E₁ ≠ 0` and `E₁ ≠ 1`: its eigenspace is bottom.
        have : f E₁ ⊓ f E₂ = (⊥ : QGIβ) := by
          simp [f, hE₁0, hE₁1]
        exact this
  · -- Completeness: the join of all eigenspaces is `⊤`.
    classical
    -- First show that the supremum is bounded above by `labPath ⊔ freePath`.
    have hSup_le : (⨆ E : ℝ, f E) ≤ labPath ⊔ freePath := by
      refine iSup_le ?_
      intro E
      by_cases h0 : E = 0
      · -- At `E = 0` the eigenspace is `labPath`.
        subst h0
        -- `labPath ≤ labPath ⊔ freePath`.
        have : (labPath : QGIβ) ≤ labPath ⊔ freePath :=
          le_sup_of_le_left le_rfl
        simpa [f] using this
      · by_cases h1 : E = 1
        · -- At `E = 1` the eigenspace is `freePath`.
          subst h1
          have : (freePath : QGIβ) ≤ labPath ⊔ freePath :=
            le_sup_of_le_right le_rfl
          simpa [f] using this
        · -- All other energies map to bottom.
          have : (⊥ : QGIβ) ≤ labPath ⊔ freePath := bot_le
          simpa [f, h0, h1] using this
    -- Next, show that the join of `labPath` and `freePath`
    -- is bounded above by the supremum.
    have hLab_le : labPath ≤ ⨆ E : ℝ, f E := by
      -- `f 0 = labPath` contributes to the supremum.
      have := le_iSup (fun E => f E) (0 : ℝ)
      simpa [f] using this
    have hFree_le : freePath ≤ ⨆ E : ℝ, f E := by
      have := le_iSup (fun E => f E) (1 : ℝ)
      simpa [f] using this
    have hJoin_le :
        labPath ⊔ freePath ≤ ⨆ E : ℝ, f E :=
      sup_le hLab_le hFree_le
    -- So the supremum of eigenspaces is exactly `labPath ⊔ freePath`.
    have hSup_eq :
        (⨆ E : ℝ, f E) = labPath ⊔ freePath :=
      le_antisymm hSup_le hJoin_le
    -- In the QGI lattice the join of the two paths is `⊤`.
    calc
      (⨆ E : ℝ, f E) = labPath ⊔ freePath := hSup_eq
      _ = (⊤ : QGIβ) := QGIInterferometer.sup_lab_free

/-- In the QGI base context, the distinguished vacuum proposition
coincides with the zero-energy eigenspace of the finite energy
observable. -/
lemma vacuum_is_ground_state_energyDemo :
    vacuum_is_ground_state (H := energyDemo) (C := QGIContext.qgiBaseContext) := by
  classical
  -- `qgiBaseContext.vacuum.vacuum` is `labPath` by construction.
  have hvac :
      QGIContext.qgiBaseContext.vacuum.vacuum = labPath := by
    -- This follows from `vacuum_qgi` in `QGIContext`.
    simp [QGIContext.qgiBaseContext, QGIContext.vacuum_qgi]
  -- The zero-energy eigenspace of `energyDemo` is also `labPath`.
  have hE0 :
      energyDemo.eigenspaces 0 = labPath := by
    simp [energyDemo]
  -- Combine the equalities.
  simpa [vacuum_is_ground_state, hvac, hE0]

/-- In the QGI base context, the Ωᴿ vacuum is the Euler boundary,
specialised to the spectral observable `energyDemo`. -/
lemma qgi_ground_is_euler :
    QGIContext.qgiBaseContext.vacuumOmega
      = QGIContext.qgiBaseContext.R.eulerBoundary :=
  ground_state_is_euler
    (H := energyDemo)
    (C := QGIContext.qgiBaseContext)
    (hground := vacuum_is_ground_state_energyDemo)

end QGI
end Quantum
end HeytingLean
