import Mathlib.Data.Set.Lattice
import Mathlib.Order.Nucleus
import Mathlib.Order.Sublocale
import Mathlib.Data.Countable.Defs

/-!
# Bauer: synthetic computability modality (Phase 2)

This file provides a **parameterized interface** for Bauer-style synthetic computability:

* Choose a truth-value frame `Ω` (a complete Heyting algebra, i.e. `Order.Frame Ω`).
* Choose a Lawvere–Tierney style modality `J : Nucleus Ω`.
* Record additional synthetic principles (Markov, enumerability, choice-like assumptions, …)
  as **structure fields**, not as global axioms.

We also include a tiny, fully-provable **demo instance** on a predicate frame `Set Bool`,
intended only as a QA-friendly executable target for downstream development.
-/

namespace HeytingLean
namespace LoF
namespace Bauer

open scoped Classical

universe u v

namespace SyntheticComputability

/-! ## Interface: a nucleus plus optional synthetic axioms -/

/-- Extra synthetic principles attached to a computability nucleus `J` on truth values `Ω`.

These are recorded as **fields** so future developments can stay parametric over which
principles hold in a given “synthetic world”. -/
structure Axioms (Ω : Type u) [Order.Frame Ω] (J : Nucleus Ω) where
  /-- Markov principle, restricted to `J`-closed (“semidecidable”) truth values. -/
  markov : ∀ p : J.toSublocale, ((p : Ω)ᶜᶜ ≤ (p : Ω))
  /-- Countability of the closed truth values (kept as an assumption, not a concrete enumerator). -/
  countable : Countable J.toSublocale
  /-- Hook for further assumptions (e.g. choice principles) recorded parametrically. -/
  choice : Prop

/-- A synthetic computability world: a nucleus on truth values plus optional axioms. -/
structure World (Ω : Type u) [Order.Frame Ω] where
  /-- The computability modality as a Lawvere–Tierney nucleus on `Ω`. -/
  J : Nucleus Ω
  /-- Additional principles (Markov, enumerability, …) attached to this world. -/
  axioms : Axioms (Ω := Ω) J

namespace World

variable {Ω : Type u} [Order.Frame Ω]
variable (W : World (Ω := Ω))

/-- The type of `J`-closed truth values, presented as a sublocale. -/
abbrev ΩJ : Type u := W.J.toSublocale

lemma markov (p : W.ΩJ) : ((p : Ω)ᶜᶜ ≤ (p : Ω)) :=
  W.axioms.markov p

lemma countable : Countable W.ΩJ :=
  W.axioms.countable

end World

/-! ## A canonical demo modality on predicate frames: adjoin a fixed core -/

namespace Predicate

variable {ι : Type v}

/-- Demo nucleus on predicates `Set ι`: adjoin a fixed “computability core” `K` by `U ↦ U ∪ K`. -/
def adjoinNucleus (K : Set ι) : Nucleus (Set ι) where
  toFun U := U ∪ K
  map_inf' U V := by
    simpa using (Set.inter_union_distrib_right U V K)
  idempotent' U := by
    intro x hx
    rcases hx with hx | hx
    · exact hx
    · exact Or.inr hx
  le_apply' U := by
    intro x hx
    exact Or.inl hx

@[simp] lemma adjoinNucleus_apply (K : Set ι) (U : Set ι) :
    adjoinNucleus (ι := ι) K U = U ∪ K := rfl

lemma adjoinNucleus_fixed_iff (K U : Set ι) :
    adjoinNucleus (ι := ι) K U = U ↔ K ⊆ U := by
  constructor
  · intro h x hx
    have : x ∈ adjoinNucleus (ι := ι) K U := by
      simpa [adjoinNucleus_apply] using (Or.inr hx : x ∈ U ∪ K)
    simpa [h] using this
  · intro hK
    ext x
    constructor
    · intro hx
      rcases hx with hxU | hxK
      · exact hxU
      · exact hK hxK
    · intro hxU
      exact Or.inl hxU

lemma mem_toSublocale_iff (K U : Set ι) :
    U ∈ (adjoinNucleus (ι := ι) K).toSublocale ↔ K ⊆ U := by
  constructor
  · intro hU
    rcases hU with ⟨V, rfl⟩
    intro x hx
    exact Or.inr hx
  · intro hK
    have hfix : adjoinNucleus (ι := ι) K U = U :=
      (adjoinNucleus_fixed_iff (ι := ι) K U).2 hK
    exact ⟨U, hfix⟩

end Predicate

/-! ## Demo world: `Set Bool` with a fixed core `{false}` -/

namespace Toy

open Predicate

/-- The fixed “computability core” in the demo model. -/
def core : Set Bool := {false}

/-- Demo computability nucleus: `U ↦ U ∪ {false}` on `Set Bool`. -/
def J : Nucleus (Set Bool) :=
  Predicate.adjoinNucleus (ι := Bool) core

/-- Closed truth values for the demo nucleus. Use `abbrev` so coercions remain definitional. -/
abbrev ΩJ : Type :=
  (J.toSublocale)

lemma memΩJ_iff (U : Set Bool) : U ∈ J.toSublocale ↔ core ⊆ U := by
  simpa [J] using (Predicate.mem_toSublocale_iff (ι := Bool) (K := core) (U := U))

def Ω0 : ΩJ :=
  ⟨core, (memΩJ_iff (U := core)).2 subset_rfl⟩

def Ωtop : ΩJ :=
  ⟨(⊤ : Set Bool), (memΩJ_iff (U := (⊤ : Set Bool))).2 (by simpa using (Set.subset_univ core))⟩

/-- Classify a closed truth value by whether `true` is in the underlying set. -/
noncomputable def toBool (p : ΩJ) : Bool := by
  classical
  exact if (true ∈ (p : Set Bool)) then true else false

def ofBool (b : Bool) : ΩJ :=
  if b then Ωtop else Ω0

noncomputable def equivBool : ΩJ ≃ Bool where
  toFun := toBool
  invFun := ofBool
  left_inv p := by
    classical
    have hcore : core ⊆ (p : Set Bool) :=
      (memΩJ_iff (U := (p : Set Bool))).1 p.property
    have hfalse : false ∈ (p : Set Bool) := by
      have : false ∈ core := by simp [core]
      exact hcore this
    by_cases htrue : true ∈ (p : Set Bool)
    · -- Then `p = Ωtop`.
      have hp : p = Ωtop := by
        apply Subtype.ext
        ext b; cases b <;> simp [Ωtop, hfalse, htrue]
      simpa [toBool, ofBool, htrue] using hp.symm
    · -- Then `p = Ω0`.
      have hp : p = Ω0 := by
        apply Subtype.ext
        ext b; cases b <;> simp [Ω0, core, hfalse, htrue]
      simpa [toBool, ofBool, htrue] using hp.symm
  right_inv b := by
    cases b <;> simp [toBool, ofBool, Ω0, Ωtop, core]

lemma countable_ΩJ : Countable ΩJ := by
  classical
  -- `ΩJ` is equivalent to `Bool`.
  exact Countable.of_equiv Bool (equivBool.symm)

lemma eq_Ω0_or_eq_Ωtop (p : ΩJ) : p = Ω0 ∨ p = Ωtop := by
  classical
  -- Every closed truth value is `Ω0` or `Ωtop`, since `ΩJ ≃ Bool`.
  have hp : ofBool (equivBool p) = p :=
    equivBool.left_inv p
  cases h : equivBool p with
  | false =>
      have hp0 : Ω0 = p := by simpa [ofBool, h] using hp
      left
      simpa using hp0.symm
  | true =>
      have hp1 : Ωtop = p := by simpa [ofBool, h] using hp
      right
      simpa using hp1.symm

def axioms : Axioms (Ω := Set Bool) J where
  markov := by
    intro p
    -- Ambient double negation is trivial for `Set Bool`.
    simp
  countable := countable_ΩJ
  choice := True

def world : World (Ω := Set Bool) where
  J := J
  axioms := axioms

end Toy

end SyntheticComputability

end Bauer
end LoF
end HeytingLean
