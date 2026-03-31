import HeytingLean.Genesis
import HeytingLean.LoF.Instances

/-!
# Genesis EigenformSoup Bridge/Gate Sanity
-/

namespace HeytingLean.Tests.Genesis

open HeytingLean
open HeytingLean.Genesis.EigenformSoup
open HeytingLean.LoF
open Set
open scoped Classical

noncomputable def idSoupNucleus : SoupNucleus where
  toFun := id
  map_inf' := by
    intro A B
    rfl
  idempotent' := by
    intro A
    rfl
  le_apply' := by
    intro A
    rfl

noncomputable def supportIdReentry : LoF.Reentry Support := by
  refine
    { nucleus := idSoupNucleus
      primordial := ({0} : Support)
      counter := ({1} : Support)
      support := ({0} : Support)
      primordial_mem := rfl
      counter_mem := rfl
      primordial_nonbot := by
        refine bot_lt_iff_ne_bot.mpr ?_
        intro h
        have hmem : (0 : Nat) ∈ (⊥ : Support) := by
          have : (0 : Nat) ∈ ({0} : Support) := by simp
          exact h ▸ this
        exact False.elim hmem
      counter_nonbot := by
        refine bot_lt_iff_ne_bot.mpr ?_
        intro h
        have hmem : (1 : Nat) ∈ (⊥ : Support) := by
          have : (1 : Nat) ∈ ({1} : Support) := by simp
          exact h ▸ this
        exact False.elim hmem
      orthogonal := by
        ext n
        constructor
        · intro hn
          rcases hn with ⟨h0, h1⟩
          have h0' : n = 0 := by simpa using h0
          have h1' : n = 1 := by simpa using h1
          have : (0 : Nat) = 1 := by
            exact h0'.symm.trans h1'
          cases Nat.zero_ne_one this
        · intro hn
          exact False.elim hn
      primordial_in_support := by
        exact le_rfl
      map_bot := rfl
      primordial_minimal := by
        intro x _hxFix hxPos hxSupport
        have hxNe : x ≠ (⊥ : Support) := by
          exact bot_lt_iff_ne_bot.mp hxPos
        have hxNonempty : x.Nonempty := Set.nonempty_iff_ne_empty.mpr (by simpa using hxNe)
        rcases hxNonempty with ⟨w, hw⟩
        have hwZero : w = 0 := by
          have hwInSupport : w ∈ ({0} : Support) := hxSupport hw
          simpa using hwInSupport
        have h0in : (0 : Nat) ∈ x := by
          exact hwZero ▸ hw
        intro n hn
        have hnZero : n = 0 := by simpa using hn
        exact hnZero ▸ h0in }

noncomputable def idBridgeWitness : ReentryBridgeWitness idSoupNucleus :=
  { reentry := supportIdReentry
    agrees := by
      intro S
      rfl }

example : BridgeReady idSoupNucleus := by
  refine ⟨idBridgeWitness, ?_⟩
  unfold ReentryBridgeLaw idSoupNucleus
  rfl

example :
    (¬ BridgeReady collapsePolicy) :=
  collapsePolicy_not_bridgeReady

noncomputable def extWithR3 : ExternalGates :=
  { boundaryNoReverseImport := True
    r3Evidence := some theoremR3ClosureEvidence }

def extMissingR3 : ExternalGates :=
  { boundaryNoReverseImport := True
    r3Evidence := none }

noncomputable example (cfg : SoupConfig) : ws9PromotionReady idSoupNucleus cfg extWithR3 := by
  refine ws9PromotionReady_of_external idSoupNucleus cfg extWithR3 trivial ?_
  exact ExternalGates.r3ClosureVerified_of_some extWithR3 rfl

noncomputable example (cfg : SoupConfig) : ¬ ws9PromotionReady idSoupNucleus cfg extMissingR3 := by
  exact ws9Promotion_not_ready_without_r3 idSoupNucleus cfg extMissingR3 rfl

end HeytingLean.Tests.Genesis
