import HeytingLean.Probability.Discrete

/-!
Finite expected-utility chooser for discrete outcome models.
- chooseArgmax over Array with a scoring function (ℝ score)
- expectedUtilityChooser: given actions, model : A → Dist Ω, utility u : Ω → ℝ,
  returns (bestIndex, bestAction, bestScore).
-/

namespace HeytingLean
namespace Probability

open HeytingLean.Math

noncomputable def chooseArgmax {α} [Inhabited α] (xs : Array α) (score : α → ℝ) : Option (Nat × α × ℝ) :=
  if xs.size = 0 then none else
    let initIdx := 0
    let initA   := xs[0]!
    let initS   := score initA
    let rec loop (i : Nat) (bestI : Nat) (bestA : α) (bestS : ℝ) : Nat × α × ℝ :=
      if i ≥ xs.size then (bestI, bestA, bestS) else
        let a := xs[i]!
        let s := score a
        if s > bestS then loop (i+1) i a s else loop (i+1) bestI bestA bestS
    some (loop 1 initIdx initA initS)

noncomputable def expectedUtilityChooser {A Ω} [Inhabited A] [Inhabited Ω]
    (actions : Array A) (model : A → Dist Ω) (u : Ω → ℝ)
    : Option (Nat × A × ℝ) :=
  chooseArgmax (α:=A) (xs := actions) (score := fun a => Dist.expect (model a) u)

end Probability
end HeytingLean
