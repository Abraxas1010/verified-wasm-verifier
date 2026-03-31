import HeytingLean.MiniC.ToLeanCP

namespace HeytingLean
namespace Tests
namespace MiniC
namespace ToLeanCPSanity

open HeytingLean.MiniC
open HeytingLean.LeanCP

example :
    ToLeanCP.compileStmtChecked (.call "step" [.var "x", .intLit 1] "ret") =
      Except.ok (.assign (.var "ret") (.call "step" [.var "x", .intLit 1])) := by
  rfl

example :
    ToLeanCP.compileStmtChecked
      (.arrayUpdate "buf" (.intLit 3) (.add (.var "x") (.intLit 1))) =
      Except.ok
        (.assign
          (.arrayAccess (.var "buf") (.intLit 3))
          (.binop .add (.var "x") (.intLit 1))) := by
  rfl

example :
    ToLeanCP.compileStmtChecked
      (.while (.var "cond") (.assign "x" (.intLit 0))) =
      Except.ok
        (.whileInv (.var "cond") HProp.htrue
          (.assign (.var "x") (.intLit 0))) := by
  rfl

example :
    ToLeanCP.compileFunDeclChecked
      { name := "demo"
        params := ["x", "y"]
        body := .return (.add (.var "x") (.var "y")) } =
      Except.ok
        { name := "demo"
          params := [("x", .int), ("y", .int)]
          retType := .int
          body := .ret (.binop .add (.var "x") (.var "y")) } := by
  rfl

end ToLeanCPSanity
end MiniC
end Tests
end HeytingLean
