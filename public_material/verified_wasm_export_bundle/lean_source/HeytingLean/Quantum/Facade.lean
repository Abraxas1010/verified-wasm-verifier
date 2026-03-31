import HeytingLean.Logic.OmegaLT
import HeytingLean.Logic.StageOML

/-
Quantum Logic Facade
- OML layer provided by `Stage.OmlCore Ω`.
- Stabilization via an LT endomap `j : Ω → Ω` (or `Reentry` adapter) to expose
  j-lifted connectives that behave Heyting-friendly on fixed points.
-/

namespace HeytingLean
namespace Quantum

open HeytingLean.Logic
open HeytingLean.Logic.OmegaLT
open HeytingLean.Logic.Stage
open HeytingLean.Logic.Stage

universe u

structure Facade (Ω : Type u) [LE Ω] [Stage.OmlCore Ω] [HeytingAlgebra Ω] where
  lt : OmegaLT.LTCore Ω

namespace Facade

variable {Ω : Type u} [LE Ω] [Stage.OmlCore Ω] [HeytingAlgebra Ω]

@[simp] def qMeet (_F : Facade Ω) (a b : Ω) : Ω :=
  Stage.OmlCore.meet a b

@[simp] def qJoin (F : Facade Ω) (a b : Ω) : Ω :=
  F.lt.ltJoin a b

@[simp] def qImp (F : Facade Ω) (a b : Ω) : Ω :=
  F.lt.ltImp a b

@[simp] def qNeg (F : Facade Ω) (a : Ω) : Ω :=
  F.lt.ltNeg a

end Facade

end Quantum
end HeytingLean
