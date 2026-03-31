import HeytingLean.BountyHunter.Solc.YulTextMini.Types

/-!
# HeytingLean.BountyHunter.Solc.YulCore.Types

`YulCore` is the long-term target: a typed, semantics-first Yul subset we can
attach correctness theorems to.

For now (phase-1 bootstrap), we alias `YulTextMini` so existing parsing and
effect-semantics infrastructure can be referenced through a stable namespace.
-/

namespace HeytingLean.BountyHunter.Solc.YulCore

abbrev Lit := HeytingLean.BountyHunter.Solc.YulTextMini.Lit
abbrev Expr := HeytingLean.BountyHunter.Solc.YulTextMini.Expr
abbrev Stmt := HeytingLean.BountyHunter.Solc.YulTextMini.Stmt
abbrev Program := HeytingLean.BountyHunter.Solc.YulTextMini.Program

end HeytingLean.BountyHunter.Solc.YulCore

