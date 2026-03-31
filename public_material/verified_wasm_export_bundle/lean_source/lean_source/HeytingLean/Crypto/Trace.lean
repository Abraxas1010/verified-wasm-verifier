import Lean
import Lean.Data.Json

namespace HeytingLean
namespace Crypto
namespace Trace

inductive Op where
  | mark
  | cross
  | process
  deriving Repr, BEq

def Op.ofString (s : String) : Option Op :=
  match s.toLower with
  | "mark"    => some .mark
  | "cross"   => some .cross
  | "process" => some .process
  | _          => none

def Op.code : Op → Nat
  | .mark    => 0
  | .cross   => 1
  | .process => 2

def digestOps (ops : List Op) : Nat :=
  let s := ops.foldl (fun acc op => acc + op.code) 0
  s % 3

def parseOpsJson (j : Lean.Json) : Option (List Op) := do
  let v ← match j.getObjVal? "ops" with
         | .ok v => some v
         | .error _ => none
  let arr ← match v.getArr? with
            | .ok a => some a
            | .error _ => none
  let mut out : List Op := []
  for v in arr.toList do
    let s ← match v.getStr? with
            | .ok s => some s
            | .error _ => none
    let op ← Op.ofString s
    out := out ++ [op]
  some out

end Trace
end Crypto
end HeytingLean
