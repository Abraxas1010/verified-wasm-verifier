import HeytingLean.Calculus.CalculusLens

/-!
Examples for the calculus lens under the minimal identity nucleus.
These are simple closed-set demonstrations that compile quickly.
-/

namespace HeytingLean
namespace Calculus

open Set

def constSet (c : ℝ) : Set (ℝ → ℝ) := { f | ∀ x, f x = c }

@[simp] lemma constSet_mem (c : ℝ) : constSet c ∈ Calculus.Instances.smoothClosureId.Omega := by
  simp [CalculusNucleus.Omega]

def affineSet (a b : ℝ) : Set (ℝ → ℝ) := { f | ∀ x, f x = a * x + b }

@[simp] lemma affineSet_mem (a b : ℝ) : affineSet a b ∈ Calculus.Instances.smoothClosureId.Omega := by
  simp [CalculusNucleus.Omega]

end Calculus
end HeytingLean
