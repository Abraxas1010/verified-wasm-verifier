import HeytingLean.MiniC.ToC

namespace HeytingLean
namespace Tests
namespace MiniC
namespace ToCSanity

open HeytingLean.MiniC

example :
    ToC.compileExprChecked (.arrayLength (.var "xs")) =
      Except.ok (C.CExpr.arrayLength "xs") := by
  rfl

example :
    ToC.compileExprChecked (.arrayIndex (.var "xs") (.intLit 2)) =
      Except.ok (C.CExpr.arrayIndex "xs" (.intLit 2)) := by
  rfl

example :
    ToC.compileExprChecked (.arrayIndex (.add (.var "xs") (.intLit 1)) (.intLit 0)) =
      Except.error (.unsupportedExpr
        "arrayIndex requires a named array variable in tiny-C lowering") := by
  rfl

example :
    ToC.compileStmtChecked (.call "f" [.var "x"] "ret") =
      Except.error (.unsupportedStmt
        "function calls are not supported in tiny-C lowering") := by
  rfl

example :
    ToC.compileStmtChecked .skip =
      Except.error (.unsupportedStmt
        "skip has no faithful tiny-C encoding in the current fragment") := by
  rfl

end ToCSanity
end MiniC
end Tests
end HeytingLean
