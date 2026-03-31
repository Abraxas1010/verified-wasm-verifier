import Lean
import Lean.Data.Json
import HeytingLean.CLI.SKYStageCore

/-!
# TypedDAGExport — Phase 1 of ProofBreeder Interactive Construction

Export Lean declarations as typed JSON: each declaration carries its type as a
**staged SExpr** (pre-bracket-abstraction form preserving `.forallE`/`.const`/`.sort`
structure) alongside the compiled SKY machine state for the proof term.

Design decisions (from hostile audit):
- Types are staged SExpr, NOT compiled SKY. Bracket abstraction destroys type structure.
- A GLOBAL InternState is shared across all declarations in a batch (H_INTERN_GLOBAL).
- `constantValueExpr?` returns `none` for `.thmInfo` (erased proofs), no panic.
- The inverse name table (Nat → Name) is included for JS consumption and Phase 4c.
-/

open Lean

namespace HeytingLean.CLI.TypedDAGExport

open HeytingLean.CLI.SKYStageCore
open HeytingLean.LoF.LeanKernel

/-- Extract the proof term from a ConstantInfo, if available.
    Theorems in Lean 4 have their proofs erased by default. -/
private def constantValueExpr? : ConstantInfo → Option Lean.Expr
  | .defnInfo info => some info.value
  | .opaqueInfo info => some info.value
  | .thmInfo _ => none
  | _ => none

/-- Classify declaration kind for the JSON output. -/
private def declKindStr : ConstantInfo → String
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- Serialize a BinderInfo to a JSON string. -/
private def binderInfoStr : HeytingLean.LoF.LeanKernel.BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

/-- Serialize a staged universe level to JSON. -/
private def stagedLevelToJson : SLevel → Json
  | .zero => Json.mkObj [("tag", "zero")]
  | .succ u => Json.mkObj [("tag", "succ"), ("level", stagedLevelToJson u)]
  | .max a b => Json.mkObj [("tag", "max"), ("left", stagedLevelToJson a), ("right", stagedLevelToJson b)]
  | .imax a b => Json.mkObj [("tag", "imax"), ("left", stagedLevelToJson a), ("right", stagedLevelToJson b)]
  | .param () => Json.mkObj [("tag", "param")]
  | .mvar () => Json.mkObj [("tag", "mvar")]

/-- Serialize a staged expression to JSON (pre-bracket-abstraction form).
    Preserves `.forallE`/`.const`/`.sort` structure for JS type checking. -/
partial def stagedExprToJson : SExpr → Json
  | .bvar idx => Json.mkObj [("tag", "bvar"), ("idx", toJson idx)]
  | .mvar () => Json.mkObj [("tag", "mvar")]
  | .sort u => Json.mkObj [("tag", "sort"), ("level", stagedLevelToJson u)]
  | .const id us => Json.mkObj [("tag", "const"), ("id", toJson id),
      ("levels", Json.arr (us.map stagedLevelToJson).toArray)]
  | .app f a => Json.mkObj [("tag", "app"), ("fn", stagedExprToJson f),
      ("arg", stagedExprToJson a)]
  | .lam n bi ty body => Json.mkObj [("tag", "lam"), ("name", toJson n),
      ("bi", Json.str (binderInfoStr bi)), ("dom", stagedExprToJson ty),
      ("body", stagedExprToJson body)]
  | .forallE n bi ty body => Json.mkObj [("tag", "forallE"), ("name", toJson n),
      ("bi", Json.str (binderInfoStr bi)), ("dom", stagedExprToJson ty),
      ("body", stagedExprToJson body)]
  | .letE n _bi ty val body => Json.mkObj [("tag", "letE"), ("name", toJson n),
      ("dom", stagedExprToJson ty), ("val", stagedExprToJson val),
      ("body", stagedExprToJson body)]
  | .lit (.natVal n) => Json.mkObj [("tag", "lit"), ("kind", "nat"), ("value", toJson n)]
  | .lit (.strVal s) => Json.mkObj [("tag", "lit"), ("kind", "str"), ("value", Json.str s)]

/-- Serialize the inverse name table (Nat → Name string) for JS and Phase 4c. -/
def nameTableToJson (st : InternState) : Json :=
  let pairs := st.names.toList.map fun (name, id) =>
    (toString id, Json.str name.toString)
  Json.mkObj pairs

/-- Build the inverse name table as a HashMap for roundtrip usage. -/
def inverseNameTable (st : InternState) : Std.HashMap Nat Name :=
  st.names.fold (init := {}) fun acc name id => acc.insert id name

/-- Compile a batch of Lean declarations to typed JSON.
    Uses a GLOBAL InternState across all declarations (H_INTERN_GLOBAL). -/
def compileTypedBatchJson
    (env : Lean.Environment)
    (maxNodes fuel : Nat)
    (declNames : Array Name) : IO (Except String Json) := do
  let mut globalSt : InternState := {}
  let mut results : Array Json := #[]
  for declName in declNames do
    let some ci := env.find? declName
      | continue
    let typeExpr := ci.type
    -- Lower projections in type
    let typeLowered ← lowerProjExpr env typeExpr
    match typeLowered with
    | .error err =>
        results := results.push (Json.mkObj
          [("name", Json.str declName.toString), ("error", Json.str err)])
        continue
    | .ok tExpr =>
        -- Stage type through global intern state
        match stageExprWithState globalSt tExpr with
        | .error err =>
            results := results.push (Json.mkObj
              [("name", Json.str declName.toString), ("error", Json.str err)])
            continue
        | .ok (stagedType, st') =>
            globalSt := st'
            -- Handle proof term (may be erased for theorems)
            match constantValueExpr? ci with
            | none =>
                -- Theorem/axiom with no available proof term
                results := results.push (Json.mkObj
                  [ ("name", Json.str declName.toString)
                  , ("kind", Json.str (declKindStr ci))
                  , ("type_staged", stagedExprToJson stagedType)
                  ])
            | some proofExpr =>
                let proofLowered ← lowerProjExpr env proofExpr
                match proofLowered with
                | .error err =>
                    results := results.push (Json.mkObj
                      [("name", Json.str declName.toString), ("error", Json.str err)])
                | .ok pExpr =>
                    match stageExprWithState globalSt pExpr with
                    | .error err =>
                        results := results.push (Json.mkObj
                          [("name", Json.str declName.toString), ("error", Json.str err)])
                    | .ok (stagedProof, st'') =>
                        globalSt := st''
                        let proofSkyJson := compileExprToStateJson maxNodes fuel stagedProof
                        results := results.push (Json.mkObj
                          [ ("name", Json.str declName.toString)
                          , ("kind", Json.str (declKindStr ci))
                          , ("type_staged", stagedExprToJson stagedType)
                          , ("proof_staged", stagedExprToJson stagedProof)
                          , ("proof_sky", match proofSkyJson with | .ok j => j | .error e => Json.str e)
                          , ("fidelity", Json.mkObj
                              [ ("erased_universe_payload", Json.bool globalSt.erasedUniversePayload)
                              , ("erased_expr_metas", Json.bool globalSt.erasedExprMetas)
                              ])
                          ])
  return .ok (Json.mkObj
    [ ("declarations", Json.arr results)
    , ("name_table", nameTableToJson globalSt)
    ])

end HeytingLean.CLI.TypedDAGExport
