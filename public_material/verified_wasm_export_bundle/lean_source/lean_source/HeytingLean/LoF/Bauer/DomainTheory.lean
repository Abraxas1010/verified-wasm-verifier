import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import HeytingLean.LoF.Bauer.SyntheticComputability

/-!
# Bauer: ω-domain theory scaffolding (Phase 1)

This file adds a small, self-contained **ω-chain complete pointed partial order** interface,
plus the Kleene-style least fixed point construction for ω-continuous endomaps.

The intent is to support Bauer-aligned “synthetic computability” narratives where fixed points
are central (recursion theorems, domain semantics), while keeping the development:

* **parametric** (no global axioms),
* **executable-friendly** (instances for complete lattices),
* and compatible with the existing nucleus-based synthetic interface.
-/

namespace HeytingLean
namespace LoF
namespace Bauer

universe u

/-! ## ωCPPO interface -/

/-- An ω-chain complete pointed partial order (ωCPPO).

We package:
* a preorder `≤`,
* a least element `⊥`,
* and a supremum operation for ω-chains (monotone sequences).
-/
class OmegaCPPO (D : Type u) [PartialOrder D] [OrderBot D] where
  /-- Supremum of an ω-chain. -/
  sup : (α : Nat → D) → Monotone α → D
  /-- Every element of the chain is below the supremum. -/
  le_sup : ∀ (α : Nat → D) (hα : Monotone α) (n : Nat), α n ≤ sup α hα
  /-- The supremum is the least upper bound. -/
  sup_le : ∀ (α : Nat → D) (hα : Monotone α) (x : D), (∀ n, α n ≤ x) → sup α hα ≤ x

namespace OmegaCPPO

variable {D : Type u} [PartialOrder D] [OrderBot D] [OmegaCPPO D]

abbrev ωSup (α : Nat → D) (hα : Monotone α) : D :=
  OmegaCPPO.sup α hα

lemma le_ωSup (α : Nat → D) (hα : Monotone α) (n : Nat) : α n ≤ ωSup α hα :=
  OmegaCPPO.le_sup α hα n

lemma ωSup_le (α : Nat → D) (hα : Monotone α) (x : D) (hx : ∀ n, α n ≤ x) :
    ωSup α hα ≤ x :=
  OmegaCPPO.sup_le α hα x hx

end OmegaCPPO

/-! ## Canonical instance: complete lattices are ωCPPOs -/

instance instOmegaCPPO_ofCompleteLattice (D : Type u) [CompleteLattice D] : OmegaCPPO D where
  sup α _ := iSup α
  le_sup α _ n := by
    exact le_iSup (fun k => α k) n
  sup_le α _ x hx := by
    exact iSup_le hx

/-! ## ω-continuity and least fixed points -/

namespace FixedPoint

open OmegaCPPO

variable {D : Type u} [PartialOrder D] [OrderBot D] [OmegaCPPO D]

/-- An endomap is ω-continuous if it is monotone and preserves ω-suprema. -/
structure OmegaContinuous (f : D → D) : Prop where
  mono : Monotone f
  map_ωSup : ∀ (α : Nat → D) (hα : Monotone α),
    f (ωSup α hα) = ωSup (fun n => f (α n)) (mono.comp hα)

namespace OmegaContinuous

lemma mono' {f : D → D} (hf : OmegaContinuous (D := D) f) : Monotone f := hf.mono

end OmegaContinuous

/-- The Kleene iteration chain `⊥, f ⊥, f (f ⊥), …` as a function `Nat → D`. -/
def kleeneChain (f : D → D) : Nat → D
  | 0 => ⊥
  | Nat.succ n => f (kleeneChain f n)

omit [OmegaCPPO D] in
@[simp] lemma kleeneChain_zero (f : D → D) : kleeneChain (D := D) f 0 = ⊥ := rfl

omit [OmegaCPPO D] in
@[simp] lemma kleeneChain_succ (f : D → D) (n : Nat) :
    kleeneChain (D := D) f (Nat.succ n) = f (kleeneChain (D := D) f n) := rfl

omit [OmegaCPPO D] in
lemma kleeneChain_le_succ {f : D → D} (hf : Monotone f) :
    ∀ n, kleeneChain (D := D) f n ≤ kleeneChain (D := D) f (n + 1)
  | 0 => by
      simp [kleeneChain]
  | Nat.succ n => by
      have ih : kleeneChain (D := D) f n ≤ kleeneChain (D := D) f (n + 1) :=
        kleeneChain_le_succ (f := f) hf n
      have h' : f (kleeneChain (D := D) f n) ≤ f (kleeneChain (D := D) f (n + 1)) :=
        hf ih
      -- rewrite both sides into the `kleeneChain` indices we need
      simpa [kleeneChain, Nat.succ_eq_add_one, Nat.add_assoc] using h'

omit [OmegaCPPO D] in
lemma monotone_kleeneChain {f : D → D} (hf : Monotone f) :
    Monotone (kleeneChain (D := D) f) :=
  monotone_nat_of_le_succ (kleeneChain_le_succ (D := D) hf)

lemma ωSup_succ_eq_ωSup_of_bot (α : Nat → D) (hα : Monotone α) (h0 : α 0 = (⊥ : D)) :
    ωSup (fun n => α (n + 1)) (hα.comp (fun _ _ hab => Nat.succ_le_succ hab))
      = ωSup α hα := by
  have hsucc : Monotone (fun n : Nat => n + 1) := fun _ _ hab => Nat.succ_le_succ hab
  apply le_antisymm
  · -- tail sup ≤ whole sup
    apply ωSup_le
    intro n
    exact le_ωSup α hα (n + 1)
  · -- whole sup ≤ tail sup
    apply ωSup_le
    intro n
    cases n with
    | zero =>
        -- α 0 = ⊥ ≤ tail sup
        simp [h0]
    | succ n =>
        -- α (n+1) is an element of the tail
        simpa using le_ωSup (fun n => α (n + 1)) (hα.comp hsucc) n

/-- Least fixed point of an ω-continuous endomap, by ω-sup of Kleene iterates from `⊥`. -/
def lfp (f : D → D) (hf : OmegaContinuous (D := D) f) : D :=
  ωSup (kleeneChain (D := D) f) (monotone_kleeneChain (D := D) hf.mono)

theorem lfp_isFixed (f : D → D) (hf : OmegaContinuous (D := D) f) :
    f (lfp (D := D) f hf) = lfp (D := D) f hf := by
  -- Use ω-continuity to pull `f` through the supremum, then show tail supremum = whole supremum.
  have hcont := hf.map_ωSup (kleeneChain (D := D) f) (monotone_kleeneChain (D := D) hf.mono)
  -- rewrite `fun n => f (kleeneChain f n)` as `kleeneChain f (n+1)`
  have hrewrite : (fun n => f (kleeneChain (D := D) f n)) = fun n => kleeneChain (D := D) f (n + 1) := by
    funext n
    cases n <;> rfl
  -- tail ωSup equals the whole ωSup since the chain starts at ⊥.
  have htail :
      ωSup (fun n => f (kleeneChain (D := D) f n)) (hf.mono.comp (monotone_kleeneChain (D := D) hf.mono))
        = ωSup (kleeneChain (D := D) f) (monotone_kleeneChain (D := D) hf.mono) := by
    -- Replace LHS by the explicit tail.
    simpa [hrewrite, lfp, kleeneChain_zero] using
      (ωSup_succ_eq_ωSup_of_bot (D := D)
        (α := kleeneChain (D := D) f)
        (hα := monotone_kleeneChain (D := D) hf.mono)
        (h0 := (kleeneChain_zero (D := D) f)))
  simpa [lfp] using hcont.trans htail

theorem lfp_le_of_isFixed (f : D → D) (hf : OmegaContinuous (D := D) f)
    {q : D} (hq : f q = q) : lfp (D := D) f hf ≤ q := by
  -- Show every Kleene iterate is ≤ q, then use `ωSup_le`.
  have hle : ∀ n, kleeneChain (D := D) f n ≤ q := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        -- f (kleeneChain n) ≤ f q = q
        have : f (kleeneChain (D := D) f n) ≤ f q := hf.mono ih
        simpa [kleeneChain, hq] using this
  exact ωSup_le (kleeneChain (D := D) f) (monotone_kleeneChain (D := D) hf.mono) q hle

end FixedPoint

/-! ## Myhill–Shepherdson-style continuity principle (Phase 2 interface) -/

namespace DomainPrinciples

open FixedPoint

variable {D : Type u} [PartialOrder D] [OrderBot D] [OmegaCPPO D]

/-- A continuity principle asserting that *every* endomap is ω-continuous.

This is the “synthetic” content typically attributed to Myhill–Shepherdson-style axioms in
domain-based synthetic computability: all maps are continuous, hence have fixed points.

We record it as a **field** (not as a global postulate) so downstream developments can remain parametric.
-/
structure ContinuityPrinciple (D : Type u) [PartialOrder D] [OrderBot D] [OmegaCPPO D] : Prop where
  omegaContinuous : ∀ f : D → D, OmegaContinuous (D := D) f

/-- Fixed point induced by the continuity principle (synthetic recursion theorem shape). -/
def fix (P : ContinuityPrinciple D) (f : D → D) : D :=
  lfp (D := D) f (P.omegaContinuous f)

theorem fix_isFixed (P : ContinuityPrinciple D) (f : D → D) :
    f (fix (D := D) P f) = fix (D := D) P f := by
  simpa [fix] using (lfp_isFixed (D := D) f (P.omegaContinuous f))

theorem fix_le_of_isFixed (P : ContinuityPrinciple D) (f : D → D) {q : D} (hq : f q = q) :
    fix (D := D) P f ≤ q := by
  simpa [fix] using (lfp_le_of_isFixed (D := D) f (P.omegaContinuous f) hq)

end DomainPrinciples

/-! ## Bauer-aligned demo example: adjoin-core nucleus on `Set Bool` -/

namespace ToyExample

open FixedPoint
open SyntheticComputability

open scoped Classical

-- Work in the complete lattice of subsets; this provides an `OmegaCPPO` instance automatically.
local instance : OmegaCPPO (Set Bool) := instOmegaCPPO_ofCompleteLattice (D := Set Bool)

def core : Set Bool := SyntheticComputability.Toy.core

  /-- Endomap `U ↦ U ∪ core` (the demo nucleus action on predicates). -/
  def adjoinCore (U : Set Bool) : Set Bool := U ⊔ core

lemma adjoinCore_mono : Monotone adjoinCore := by
  intro U V hUV
  exact sup_le_sup_right hUV core

lemma adjoinCore_ωcontinuous : OmegaContinuous (D := Set Bool) adjoinCore where
  mono := adjoinCore_mono
  map_ωSup := by
    intro α _
    -- In complete lattices, `iSup_sup` provides `(⨆ n, α n) ⊔ core = ⨆ n, α n ⊔ core`.
    simpa [OmegaCPPO.ωSup, instOmegaCPPO_ofCompleteLattice, adjoinCore] using
      (iSup_sup (f := α) (a := core))

lemma core_isFixed : adjoinCore core = core := by
  simp [adjoinCore]

theorem lfp_adjoinCore_eq_core :
    lfp (D := Set Bool) adjoinCore adjoinCore_ωcontinuous = core := by
  apply le_antisymm
  · -- minimality: lfp ≤ core because core is a fixed point
    exact lfp_le_of_isFixed (D := Set Bool) adjoinCore adjoinCore_ωcontinuous core_isFixed
  · -- core ≤ lfp by `le_sup` at iteration 1
    -- `kleeneChain adjoinCore 1 = core`
    have : core ≤ lfp (D := Set Bool) adjoinCore adjoinCore_ωcontinuous := by
      -- `le_ωSup` at `n=1`
      have hle := OmegaCPPO.le_ωSup (D := Set Bool)
        (α := kleeneChain (D := Set Bool) adjoinCore)
        (hα := monotone_kleeneChain (D := Set Bool) adjoinCore_mono)
        1
      -- simplify the chain element
      simpa [lfp, kleeneChain, adjoinCore, core] using hle
    exact this

end ToyExample

end Bauer
end LoF
end HeytingLean
