import Mathlib.Analysis.Quaternion
import HeytingLean.ClosingTheLoop.Semantics.NucleusBridge
import HeytingLean.Generative.SpinorBridge.ClosureSDK.HopfCoordinates

noncomputable section

open Set
open scoped Quaternion

namespace HeytingLean.ClosingTheLoop.Semantics

abbrev ClosureSDKQ := Quaternion ℝ

/-- Distinguished sigma-zero witnesses `{1, -1}` from the Closure SDK surface. -/
def coherencePoles : Set ClosureSDKQ :=
  {q | q = (1 : ClosureSDKQ) ∨ q = (-1 : ClosureSDKQ)}

/-- A minimal truthful closure operator: adjoin the distinguished poles to any diagnostic set. -/
def closureSDKNucleus : Nucleus (Set ClosureSDKQ) :=
  addClosureNucleus coherencePoles

@[simp] theorem mem_coherencePoles (q : ClosureSDKQ) :
    q ∈ coherencePoles ↔ q = (1 : ClosureSDKQ) ∨ q = (-1 : ClosureSDKQ) :=
  Iff.rfl

theorem sigma_zero_of_mem_coherencePoles {q : ClosureSDKQ} (hq : q ∈ coherencePoles) :
    HeytingLean.Generative.SpinorBridge.ClosureSDK.sigma q = 0 := by
  rcases hq with rfl | rfl
  · exact HeytingLean.Generative.SpinorBridge.ClosureSDK.sigma_one
  · exact HeytingLean.Generative.SpinorBridge.ClosureSDK.sigma_neg_one

@[simp] theorem closureSDKNucleus_apply (S : Set ClosureSDKQ) :
    closureSDKNucleus S = S ∪ coherencePoles :=
  rfl

theorem coherencePoles_subset_closed (S : Set ClosureSDKQ) :
    coherencePoles ⊆ closureSDKNucleus S := by
  intro q hq
  exact Or.inr hq

theorem closureSDKNucleus_fixed_iff (S : Set ClosureSDKQ) :
    closureSDKNucleus S = S ↔ coherencePoles ⊆ S := by
  constructor
  · intro h q hq
    have hmem : q ∈ closureSDKNucleus S := by
      exact coherencePoles_subset_closed S hq
    simpa [h] using hmem
  · intro h
    ext q
    constructor
    · intro hq
      rcases hq with hq | hq
      · exact hq
      · exact h hq
    · intro hq
      exact Or.inl hq

@[simp] theorem one_mem_closureSDKNucleus (S : Set ClosureSDKQ) :
    (1 : ClosureSDKQ) ∈ closureSDKNucleus S := by
  exact coherencePoles_subset_closed S (by simp [coherencePoles])

@[simp] theorem neg_one_mem_closureSDKNucleus (S : Set ClosureSDKQ) :
    (-1 : ClosureSDKQ) ∈ closureSDKNucleus S := by
  exact coherencePoles_subset_closed S (by simp [coherencePoles])

end HeytingLean.ClosingTheLoop.Semantics
