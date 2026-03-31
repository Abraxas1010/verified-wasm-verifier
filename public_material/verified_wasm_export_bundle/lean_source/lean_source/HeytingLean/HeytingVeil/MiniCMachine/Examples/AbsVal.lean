import HeytingLean.HeytingVeil.MiniCMachine.Decidable

namespace HeytingLean
namespace HeytingVeil
namespace MiniCMachine
namespace Examples

def absFun : MiniC.Fun :=
  {
    name := "abs_i64"
    params := ["x"]
    body :=
      .if_ (.le (.var "x") (.intLit (-1)))
        (.return (.sub (.intLit 0) (.var "x")))
        (.return (.var "x"))
  }

def absDomain : BoundedDomain :=
  { vars := [("x", -10, 10)] }

def absMachine : ModelCheck.DecidableMachine ProgramConfig :=
  boundedMiniCMachine absFun [] absDomain

def absReturnNonnegative : ProgramConfig → Prop
  | ⟨σ, _, .return e⟩ => 0 ≤ e.eval (σ.toTotalStore)
  | _ => True

instance : DecidablePred absReturnNonnegative := by
  intro cfg
  cases cfg with
  | mk σ _ cont =>
      cases cont <;> simp [absReturnNonnegative] <;> infer_instance

#eval checkSafety absMachine absReturnNonnegative 12

end Examples
end MiniCMachine
end HeytingVeil
end HeytingLean
