import Lean
import Std

/-!
# HeytingLean.BountyHunter.Solc.YulObjectMini.Types

Minimal AST for Yul *object* syntax (`object` / `code` / `data`) as emitted by solc `ir` / `irOptimized`.

We intentionally keep `code` bodies as raw strings in v0; they are canonicalized separately by
passing the text through the existing function-body canonicalizer (and YulTextMini for bodies).
-/

namespace HeytingLean.BountyHunter.Solc.YulObjectMini

inductive DataValue where
  | str (s : String)
  | hex (s : String)
  deriving Repr, Inhabited

inductive Item where
  | object (name : String) (items : Array Item)
  | code (body : String)
  | data (name : String) (value : DataValue)
  deriving Repr, Inhabited

structure Program where
  version : String := "yulobjectmini.v0"
  items : Array Item := #[]
  deriving Repr, Inhabited

end HeytingLean.BountyHunter.Solc.YulObjectMini
