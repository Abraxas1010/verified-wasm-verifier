import HeytingLean.Cybernetics.Observer

/-
Second-Order Cybernetics: Feedback primitives and closed-loop composition.
-/

namespace HeytingLean
namespace Cybernetics

universe u

structure Feedback (Sys : Type u) (Obs : Type u) where
  step : Sys → Obs → Sys

namespace Feedback
variable {Sys Obs : Type u}

@[simp] def loop (O : Observer Obs Sys) (F : Feedback Sys Obs) (s : Sys) : Sys :=
  F.step s (O.observe s)

end Feedback

end Cybernetics
end HeytingLean

