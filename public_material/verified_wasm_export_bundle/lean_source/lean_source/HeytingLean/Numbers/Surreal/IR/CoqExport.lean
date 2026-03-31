import Lean.Data.Json
import HeytingLean.Numbers.Surreal.LoFProgram

/-!
# Coq-friendly IR export for finite Surreal LoF programs

This module provides a tiny JSON-serializable IR intended to be replayed in other
systems (e.g. Coq) as a cross-check that the *program shape* matches.

Scope:
- This export targets the **finite** LoF DSL (`LoFProgram.Program`) used by the
  current executable surreal pipeline.
- The IR is intentionally minimal: it records `{L|R}` cuts as index lists.
- Digest parity and proof transport across provers is out of scope here, but this
  file is the stable foundation for it.
-/

namespace HeytingLean
namespace Numbers
namespace Surreal
namespace IR

open Lean
open HeytingLean.Numbers.Surreal.LoFProgram

/-! ## IR types -/

inductive CoqOp where
  | void
  | cut (L R : List Nat)
  deriving Repr, DecidableEq

structure CoqSurrealIR where
  version : String := "1.0"
  format : String := "coq-surreal-ir"
  operations : List CoqOp
  root : Nat
  deriving Repr, DecidableEq

/-! ## JSON encoding -/

instance : ToJson CoqOp where
  toJson
    | .void =>
        Json.mkObj [("type", Json.str "void")]
    | .cut L R =>
        Json.mkObj
          [ ("type", Json.str "cut")
          , ("left", Json.arr <| (L.map (fun (n : Nat) => Json.num (n : JsonNumber))).toArray)
          , ("right", Json.arr <| (R.map (fun (n : Nat) => Json.num (n : JsonNumber))).toArray)
          ]

instance : ToJson CoqSurrealIR where
  toJson ir :=
    Json.mkObj
      [ ("version", Json.str ir.version)
      , ("format", Json.str ir.format)
      , ("operations", Json.arr <| (ir.operations.map toJson).toArray)
      , ("root", Json.num ir.root)
      ]

/-! ## Export -/

def toCoqIR (p : Program) : CoqSurrealIR :=
  let ops :=
    p.ops.toList.map fun op =>
      match op with
      | .unmark => CoqOp.void
      | .mark L R => CoqOp.cut L R
  { operations := ops, root := p.root }

end IR
end Surreal
end Numbers
end HeytingLean
