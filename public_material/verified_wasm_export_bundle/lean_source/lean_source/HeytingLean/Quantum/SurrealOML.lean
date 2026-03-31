import Mathlib.Data.Set.Lattice
import HeytingLean.Numbers.SurrealCore
import HeytingLean.Numbers.Surreal.Nucleus
import HeytingLean.LoF.Instances
import HeytingLean.Quantum.OML.Sasaki

/-
# Surreal orthomodular lattice façade

This module packages the Boolean / orthomodular lattice structure on
`Set SurrealCore.PreGame` for use as an OML carrier in quantum / Ωᴿ
bridges. It does not introduce new structure; rather, it re-exports
the existing instances provided by:

* `Set`’s Boolean algebra on `PreGame`,
* the canonical `OrthocomplementedLattice` / `OrthomodularLattice`
  structure on any Boolean algebra (from `OML.Sasaki`),
* the `PrimaryAlgebra` instance for powersets from `LoF.Instances`.

Direction 6 (Surreal / game-theoretic instantiation) will use this
carrier as `β := Surrealβ` and `α := Set SurrealCore.PreGame` inside
`VacuumOmegaRContext`, tying the abstract vacuum/Euler-boundary
equivalence to Conway birthdays.
-/

namespace HeytingLean
namespace Quantum

open HeytingLean.Numbers
open HeytingLean.Numbers.SurrealCore
open HeytingLean.Numbers.Surreal

/-- Surreal OML carrier: sets of pre-games, equipped with the Boolean /
orthomodular lattice structure inherited from `Set`. -/
abbrev Surrealβ := Set PreGame

namespace SurrealOML

open HeytingLean.Quantum.OML

/-!
The following instances are *definitionally* inherited:

* `BooleanAlgebra (Set PreGame)` from `Mathlib.Data.Set.Lattice`,
* `OrthocomplementedLattice (Set PreGame)` and
  `OrthomodularLattice (Set PreGame)` from `instOrthocomplementedLatticeOfBoolean`
  and `instOrthomodularLatticeOfBoolean`.

We mark them here for discoverability in the quantum layer.
-/

instance instOrthocomplementedLatticeSurreal :
    OrthocomplementedLattice Surrealβ :=
  instOrthocomplementedLatticeOfBoolean (α := Surrealβ)

instance instOrthomodularLatticeSurreal :
    OrthomodularLattice Surrealβ :=
  instOrthomodularLatticeOfBoolean (α := Surrealβ)

/-! ### Basic Boolean / OML facts for surreal subsets -/

open Set

/-- Bottom and top in the surreal carrier coincide with `∅` and `univ`. -/
@[simp] lemma bot_eq_empty : (⊥ : Surrealβ) = (∅ : Set PreGame) := rfl

@[simp] lemma top_eq_univ : (⊤ : Surrealβ) = (Set.univ : Set PreGame) := rfl

/-- Singleton set containing the Conway null cut `{∅ ∣ ∅}`. -/
def nullCutSet : Surrealβ := { g | g = nullCut }

@[simp] lemma mem_nullCutSet {g : PreGame} :
    g ∈ nullCutSet ↔ g = nullCut := by
  rfl

@[simp] lemma nullCut_mem_nullCutSet : nullCut ∈ nullCutSet := by
  simp [nullCutSet]

/-- The singleton null-cut set is non-empty and not bottom. -/
lemma nullCutSet_nonempty : (nullCutSet : Surrealβ).Nonempty := by
  refine ⟨nullCut, ?_⟩
  exact nullCut_mem_nullCutSet

lemma bot_ne_nullCutSet : (⊥ : Surrealβ) ≠ nullCutSet := by
  intro h
  have : nullCut ∈ (⊥ : Surrealβ) := by
    have : nullCut ∈ nullCutSet := nullCut_mem_nullCutSet
    simpa [h, bot_eq_empty] using this
  simpa [bot_eq_empty] using this

/-- In the surreal Boolean algebra, `A ⊓ Aᶜ = ⊥` and `A ⊔ Aᶜ = ⊤`.
We record these facts for the null-cut singleton. -/
@[simp] lemma inf_compl_nullCutSet :
    (nullCutSet : Surrealβ) ⊓ nullCutSetᶜ = ⊥ := by
  simpa [nullCutSet] using
    (inf_compl_self (s := { g : PreGame | g = nullCut }))

@[simp] lemma sup_compl_nullCutSet :
    (nullCutSet : Surrealβ) ⊔ nullCutSetᶜ = ⊤ := by
  simpa [nullCutSet] using
    (sup_compl_self (s := { g : PreGame | g = nullCut }))

/-- The complement of the null-cut singleton is non-bottom. -/
lemma compl_nullCutSet_ne_bot :
    (nullCutSetᶜ : Surrealβ) ≠ (⊥ : Surrealβ) := by
  classical
  intro h
  -- Exhibit a concrete pre-game not equal to `nullCut`.
  let g : PreGame := PreGame.build [] []
  have hne : g ≠ nullCut := by
    intro hEq
    have hb := congrArg birthday hEq
    -- `nullCut` has birthday 0, while `build [] []` has birthday 1.
    have : False := by
      simpa [birthday, nullCut, g, PreGame.build, PreGame.maxBirth] using hb
    exact this
  have hmem : g ∈ (nullCutSetᶜ : Surrealβ) := by
    simp [nullCutSet, hne]
  -- But the complement being bottom would force `g` to lie in `∅`.
  have : g ∈ (⊥ : Surrealβ) := by simpa [h] using hmem
  simpa [bot_eq_empty] using this

/-- Canonical legal core as an inhabitant of the surreal OML carrier. -/
def canonicalCoreSet : Surrealβ := Surreal.Int.C

@[simp] lemma canonicalCoreSet_def :
    canonicalCoreSet = Surreal.Int.C := rfl

@[simp] lemma inf_compl_canonicalCoreSet :
    (canonicalCoreSet : Surrealβ) ⊓ canonicalCoreSetᶜ = ⊥ := by
  simpa [canonicalCoreSet] using
    (inf_compl_self (s := Surreal.Int.C))

@[simp] lemma sup_compl_canonicalCoreSet :
    (canonicalCoreSet : Surrealβ) ⊔ canonicalCoreSetᶜ = ⊤ := by
  simpa [canonicalCoreSet] using
    (sup_compl_self (s := Surreal.Int.C))

end SurrealOML

end Quantum
end HeytingLean
