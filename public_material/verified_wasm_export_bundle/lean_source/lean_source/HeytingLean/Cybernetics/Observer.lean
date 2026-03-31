import HeytingLean.Logic.StageSemantics

/-
Second-Order Cybernetics: Observer primitives.
Defines observers of systems and observers of observers (observation of observation),
plus staged helpers across a Bridge.
-/

namespace HeytingLean
namespace Cybernetics

universe u

structure Observer (Obs : Type u) (Sys : Type u) where
  observe : Sys → Obs

namespace Observer
variable {Obs Sys : Type u}

/-- Identity observer on `Obs`. -/
@[simp] def idObs : Observer Obs Obs :=
  { observe := id }

end Observer

/-! ### Bridge helpers -/

namespace Stage

open HeytingLean.Logic.Stage

variable {α Ω : Type u} [LE α] [LE Ω]

@[simp] def observeStage (B : Bridge α Ω)
    (O : Observer Ω Ω) (x : α) : Ω :=
  O.observe (B.shadow x)

@[simp] def observeLift (B : Bridge α Ω)
    (O : Observer Ω Ω) (x : α) : α :=
  B.lift (O.observe (B.shadow x))

end Stage

end Cybernetics
end HeytingLean
