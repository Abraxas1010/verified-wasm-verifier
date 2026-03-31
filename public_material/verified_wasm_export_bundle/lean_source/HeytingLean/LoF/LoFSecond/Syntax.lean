/-!
# LoFSecond.Syntax — primary syntax + re-entry constant

This module extends `LoFPrimary.Syntax` with a distinguished constant `reentry`,
intended to model Spencer–Brown’s “re-entry” (second-degree) phenomenon.

The primary calculus (calling/crossing/void absorption) is still encoded as in
`LoFPrimary`, but now the language can also mention `reentry`.

Semantics and rewrite soundness are provided in `LoFSecond.Normalization`.
-/

namespace HeytingLean
namespace LoF
namespace LoFSecond

/-! ## Syntax -/

/-- Second-degree LoF expressions with `n` free variables. -/
inductive Expr (n : Nat) where
  | void : Expr n
  | var : Fin n → Expr n
  | mark : Expr n → Expr n
  | juxt : Expr n → Expr n → Expr n
  | reentry : Expr n
  deriving DecidableEq, Repr

namespace Expr

variable {n : Nat}

/-- The marked constant (often written as an empty mark). -/
def marked : Expr n :=
  mark void

end Expr

end LoFSecond
end LoF
end HeytingLean

