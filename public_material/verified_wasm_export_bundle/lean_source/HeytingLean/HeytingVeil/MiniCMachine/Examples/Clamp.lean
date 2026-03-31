import HeytingLean.HeytingVeil.MiniCMachine.Decidable

namespace HeytingLean
namespace HeytingVeil
namespace MiniCMachine
namespace Examples

def clampFun : MiniC.Fun :=
  {
    name := "clamp_i64"
    params := ["x", "lo", "hi"]
    body :=
      .if_ (.le (.var "x") (.sub (.var "lo") (.intLit 1)))
        (.return (.var "lo"))
        (.if_ (.le (.var "hi") (.sub (.var "x") (.intLit 1)))
          (.return (.var "hi"))
          (.return (.var "x")))
  }

def clampDomain : BoundedDomain :=
  { vars := [("x", 0, 7), ("lo", 0, 7), ("hi", 0, 7)] }

def clampMachine : ModelCheck.DecidableMachine ProgramConfig :=
  boundedMiniCMachine clampFun [] clampDomain

def clampWithinBounds : ProgramConfig → Prop
  | ⟨σ, _, .return e⟩ =>
      let st := σ.toTotalStore
      let lo := st "lo"
      let hi := st "hi"
      let v := e.eval st
      if lo ≤ hi then lo ≤ v ∧ v ≤ hi else True
  | _ => True

instance : DecidablePred clampWithinBounds := by
  intro cfg
  cases cfg with
  | mk σ _ cont =>
      cases cont <;> simp [clampWithinBounds] <;> infer_instance

#eval checkSafety clampMachine clampWithinBounds 12

end Examples
end MiniCMachine
end HeytingVeil
end HeytingLean
