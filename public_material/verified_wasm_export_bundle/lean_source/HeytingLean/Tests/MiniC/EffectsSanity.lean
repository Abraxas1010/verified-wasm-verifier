import Mathlib.Tactic
import HeytingLean.MiniC.Effects
import HeytingLean.C.Syntax

namespace HeytingLean
namespace Tests
namespace MiniC
namespace Effects

open HeytingLean.MiniC

private def ioAbsStmt : Stmt :=
  .seq
    (MiniC.Effects.readInput "x" "req")
    (.seq
      (.if_
        (.le (.var "x") (.intLit (-1)))
        (.assign "y" (.sub (.intLit 0) (.var "x")))
        (.assign "y" (.var "x")))
      (.seq
        (MiniC.Effects.writeOutput "resp" (.var "y"))
        (.return (.var "y"))))

private def inputStore (n : Int) : Store :=
  update emptyStore (MiniC.Effects.inputSlot "req") (.int n)

private def runReturnedInt (n : Int) : Option Int :=
  match execWithDefs [] ioAbsStmt (inputStore n) 64 with
  | some (.returned (.int k)) => some k
  | _ => none

example :
    runReturnedInt (-5) = some 5 := by
  native_decide

example :
    runReturnedInt 3 = some 3 := by
  native_decide

example :
    MiniC.Effects.outputNonnegative
      (update emptyStore (MiniC.Effects.outputSlot "resp") (.int 7)) "resp" := by
  simp [MiniC.Effects.outputNonnegative, lookup]

example :
    ToC.compileStmt (MiniC.Effects.readInput "x" "req") =
      C.CStmt.assign "x" (C.CExpr.var (MiniC.Effects.inputSlot "req")) := by
  rfl

example :
    ToC.compileStmt (MiniC.Effects.writeOutput "resp" (.var "y")) =
      C.CStmt.assign (MiniC.Effects.outputSlot "resp") (C.CExpr.var "y") := by
  rfl

end Effects
end MiniC
end Tests
end HeytingLean
