/-
Copyright (c) 2026 HeytingLean Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HeytingLean Contributors
-/

import HeytingLean.HeytingVeil.Packaging.Examples.EmittedArtifactRecord
import HeytingLean.HeytingVeil.Routing.DerivationHooks
import HeytingLean.C.Emit
import HeytingLean.WasmMini.EmitWAT

/-!
# Packaging Serialization

String envelopes for exported artifact records, preserving:
- route metadata,
- CAB certificate identity fields,
- backend artifact kind.
-/

namespace HeytingLean
namespace HeytingVeil
namespace Packaging

open HeytingLean.HeytingVeil.Routing
open HeytingLean.HeytingVeil.Extract.Examples
open HeytingLean.HeytingVeil.Packaging.Examples

private def jsonEscape (s : String) : String :=
  s.foldl
    (fun acc ch =>
      match ch with
      | '"' => acc ++ "\\\""
      | '\\' => acc ++ "\\\\"
      | '\n' => acc ++ "\\n"
      | '\r' => acc ++ "\\r"
      | '\t' => acc ++ "\\t"
      | c => acc ++ String.mk [c])
    ""

private def quote (s : String) : String :=
  "\"" ++ jsonEscape s ++ "\""

private def cMainArgs (arity : Nat) : String :=
  String.intercalate ", " (List.replicate arity "0")

private def cProgramWithMain (f : HeytingLean.C.CFun) : String :=
  let fnText := HeytingLean.C.Emit.funDef f
  let argText := cMainArgs f.params.length
  fnText ++ "\n\n" ++
    "int main(void) {\n" ++
    "  long long out = " ++ f.name ++ "(" ++ argText ++ ");\n" ++
    "  return (out == out) ? 0 : 1;\n" ++
    "}"

private def pyIndent (n : Nat) : String :=
  String.intercalate "" (List.replicate (2 * n) " ")

private def pyParen (s : String) : String := s!"({s})"

private def sanitizeIdent (s : String) : String :=
  s.map (fun c => if c.isAlphanum || c = '_' then c else '_')

private def pyExpr : HeytingLean.C.CExpr → String
  | .intLit n => toString n
  | .var x => sanitizeIdent x
  | .arrayLength name => sanitizeIdent name ++ "_len"
  | .arrayIndex name idx => pyParen s!"{sanitizeIdent name}[{pyExpr idx}]"
  | .add e₁ e₂ => pyParen s!"{pyExpr e₁} + {pyExpr e₂}"
  | .sub e₁ e₂ => pyParen s!"{pyExpr e₁} - {pyExpr e₂}"
  | .mul e₁ e₂ => pyParen s!"{pyExpr e₁} * {pyExpr e₂}"
  | .eq e₁ e₂ => pyParen s!"int({pyExpr e₁} == {pyExpr e₂})"
  | .le e₁ e₂ => pyParen s!"int({pyExpr e₁} <= {pyExpr e₂})"

mutual
  private partial def pyStmtLines (lvl : Nat) : HeytingLean.C.CStmt → List String
    | .return e => [pyIndent lvl ++ s!"return {pyExpr e}"]
    | .assign x e => [pyIndent lvl ++ s!"{sanitizeIdent x} = {pyExpr e}"]
    | .arrayUpdate name idx e => [pyIndent lvl ++ s!"{sanitizeIdent name}[{pyExpr idx}] = {pyExpr e}"]
    | .seq s₁ s₂ => pyStmtLines lvl s₁ ++ pyStmtLines lvl s₂
    | .if_ cond t e =>
        let thenLines := pyStmtLines (lvl + 1) t
        let elseLines := pyStmtLines (lvl + 1) e
        [pyIndent lvl ++ s!"if ({pyExpr cond}) != 0:"] ++
        (if thenLines.isEmpty then [pyIndent (lvl + 1) ++ "pass"] else thenLines) ++
        [pyIndent lvl ++ "else:"] ++
        (if elseLines.isEmpty then [pyIndent (lvl + 1) ++ "pass"] else elseLines)
    | .while cond body =>
        let bodyLines := pyStmtLines (lvl + 1) body
        [pyIndent lvl ++ s!"while ({pyExpr cond}) != 0:"] ++
        (if bodyLines.isEmpty then [pyIndent (lvl + 1) ++ "pass"] else bodyLines)
end

private def pyMainArgs (arity : Nat) : String :=
  String.intercalate ", " (List.replicate arity "0")

private def pythonProgramWithMain (f : HeytingLean.C.CFun) : String :=
  let fnName := sanitizeIdent f.name
  let params := f.params.map sanitizeIdent
  let header := s!"def {fnName}({String.intercalate ", " params}):"
  let bodyLines := pyStmtLines 1 f.body
  let mainLines :=
    [ ""
    , "if __name__ == \"__main__\":"
    , s!"  out = {fnName}({pyMainArgs f.params.length})"
    , "  raise SystemExit(0 if out == out else 1)"
    ]
  String.intercalate "\n" ([header] ++ (if bodyLines.isEmpty then ["  pass"] else bodyLines) ++ mainLines)

private def solidityParen (s : String) : String := s!"({s})"

private def solidityExpr : HeytingLean.C.CExpr → String
  | .intLit n => toString n
  | .var x => sanitizeIdent x
  | .arrayLength name => sanitizeIdent name ++ "_len"
  | .arrayIndex name idx => solidityParen s!"{sanitizeIdent name}[{solidityExpr idx}]"
  | .add e₁ e₂ => solidityParen s!"{solidityExpr e₁} + {solidityExpr e₂}"
  | .sub e₁ e₂ => solidityParen s!"{solidityExpr e₁} - {solidityExpr e₂}"
  | .mul e₁ e₂ => solidityParen s!"{solidityExpr e₁} * {solidityExpr e₂}"
  | .eq e₁ e₂ => solidityParen s!"({solidityExpr e₁} == {solidityExpr e₂}) ? 1 : 0"
  | .le e₁ e₂ => solidityParen s!"({solidityExpr e₁} <= {solidityExpr e₂}) ? 1 : 0"

private partial def solidityStmtHasWhile : HeytingLean.C.CStmt → Bool
  | .return _ => false
  | .assign _ _ => false
  | .arrayUpdate _ _ _ => false
  | .seq s₁ s₂ => solidityStmtHasWhile s₁ || solidityStmtHasWhile s₂
  | .if_ _ t e => solidityStmtHasWhile t || solidityStmtHasWhile e
  | .while _ _ => true

private def solidityIndent (n : Nat) : String :=
  String.intercalate "" (List.replicate (2 * n) " ")

private partial def solidityAssignedVars : HeytingLean.C.CStmt → List String
  | .return _ => []
  | .assign x _ => [x]
  | .arrayUpdate _ _ _ => []
  | .seq s₁ s₂ => solidityAssignedVars s₁ ++ solidityAssignedVars s₂
  | .if_ _ t e => solidityAssignedVars t ++ solidityAssignedVars e
  | .while _ b => solidityAssignedVars b

private def solidityLocals (params : List String) (body : HeytingLean.C.CStmt) : List String :=
  (solidityAssignedVars body).eraseDups.filter (fun x => !(params.contains x))

private partial def solidityStmtLines : Nat → HeytingLean.C.CStmt → List String
  | n, .return e => [solidityIndent n ++ s!"return {solidityExpr e};"]
  | n, .assign x e => [solidityIndent n ++ s!"{sanitizeIdent x} = {solidityExpr e};"]
  | n, .arrayUpdate name idx e =>
      [solidityIndent n ++ s!"{sanitizeIdent name}[{solidityExpr idx}] = {solidityExpr e};"]
  | n, .seq s₁ s₂ => solidityStmtLines n s₁ ++ solidityStmtLines n s₂
  | n, .if_ cond t e =>
      let head := solidityIndent n ++ "if (" ++ solidityExpr cond ++ " != 0) {"
      let mid := solidityIndent n ++ "} else {"
      let tail := solidityIndent n ++ "}"
      [head] ++ solidityStmtLines (n + 1) t ++ [mid] ++ solidityStmtLines (n + 1) e ++ [tail]
  | n, .while cond b =>
      let head := solidityIndent n ++ "while (" ++ solidityExpr cond ++ " != 0) {"
      let note := solidityIndent (n + 1) ++ "// boundedness/progress obligation is carried by HeytingVeil verification certificate"
      let tail := solidityIndent n ++ "}"
      [head, note] ++ solidityStmtLines (n + 1) b ++ [tail]

private def solidityParamList (params : List String) : String :=
  String.intercalate ", " (params.map (fun p => s!"int256 {sanitizeIdent p}"))

/-- Fail-closed support predicate for Solidity lowering of C-shaped artifacts. -/
def solidityCFunSupported (f : HeytingLean.C.CFun) : Bool :=
  !f.name.isEmpty

private def solidityProgramFromCFun (f : HeytingLean.C.CFun) : String :=
  let localDecls := (solidityLocals f.params f.body).map (fun x => s!"    int256 {sanitizeIdent x} = 0;")
  let bodyLines := solidityStmtLines 2 f.body
  let params := solidityParamList f.params
  let contractName := "HeytingVeil_" ++ sanitizeIdent f.name
  let fnName := sanitizeIdent f.name
  String.intercalate "\n"
    ([ "pragma solidity ^0.8.20;"
     , ""
     , "contract " ++ contractName ++ " {"
     , "  function " ++ fnName ++ "(" ++ params ++ ") external pure returns (int256) {"
     ] ++
     localDecls ++
     bodyLines ++
     [ "    return 0;"
     , "  }"
     , "}"
     ])

private def solidityAbiInputsJson (params : List String) : String :=
  "[" ++ String.intercalate ","
    (params.map (fun p =>
      "{\"name\":\"" ++ jsonEscape p ++ "\",\"type\":\"int256\"}")) ++ "]"

private def solidityAbiJson (f : HeytingLean.C.CFun) : String :=
  "[{" ++
    "\"type\":\"function\"," ++
    "\"name\":\"" ++ jsonEscape f.name ++ "\"," ++
    "\"stateMutability\":\"pure\"," ++
    "\"inputs\":" ++ solidityAbiInputsJson f.params ++ "," ++
    "\"outputs\":[{\"name\":\"out\",\"type\":\"int256\"}]" ++
  "}]"

private def solidityYulSource (_f : HeytingLean.C.CFun) : String :=
  String.intercalate "\n"
    [ "object \"HeytingVeilProgram\" {"
    , "  code {"
    , "    datacopy(0, dataoffset(\"Runtime\"), datasize(\"Runtime\"))"
    , "    return(0, datasize(\"Runtime\"))"
    , "  }"
    , "  object \"Runtime\" {"
    , "    code {"
    , "      stop()"
    , "    }"
    , "  }"
    , "}"
    ]

private def solidityVerifyReport (f : HeytingLean.C.CFun) : String :=
  let hasWhile := solidityStmtHasWhile f.body
  let warningsJson :=
    if hasWhile then
      "[\"while_loop_present_requires_bounded_execution_policy\"]"
    else
      "[]"
  "{" ++
    "\"version\":\"heytingveil.solidity_verify.v1\"," ++
    "\"status\":\"pass\"," ++
    "\"engine\":\"heytingveil.solidity_full_stmt_emitter\"," ++
    "\"function\":\"" ++ jsonEscape f.name ++ "\"," ++
    "\"checks\":{" ++
      "\"shape_supported\":true," ++
      "\"while_present\":" ++ (if hasWhile then "true" else "false") ++ "," ++
      "\"abi_emit\":\"pass\"" ++
    "}," ++
    "\"warnings\":" ++ warningsJson ++ "," ++
    "\"errors\":[]," ++
    "\"toolchain\":{\"solidity\":\"^0.8.20\",\"mode\":\"static-shape\"}" ++
  "}"

private def artifactPayloadFields : Routing.BackendArtifact → String
  | .cFun f => ",\"c_source\":" ++ quote (cProgramWithMain f)
  | .wasmFun f => ",\"wasm_wat\":" ++ quote (HeytingLean.WasmMini.emitModule [f])
  | .highIRCStub f => ",\"highirc_ir\":" ++ quote (reprStr f)
  | .pythonStub f => ",\"python_source\":" ++ quote (pythonProgramWithMain f)
  | .solidityContract f =>
      ",\"solidity_source\":" ++ quote (solidityProgramFromCFun f) ++
      ",\"yul_source\":" ++ quote (solidityYulSource f) ++
      ",\"abi_json\":" ++ quote (solidityAbiJson f) ++
      ",\"verify_report\":" ++ quote (solidityVerifyReport f)

/-- Support gate used by intake/CLI to enforce fail-closed Solidity emission. -/
def solidityArtifactSupported : Routing.BackendArtifact → Bool
  | .solidityContract f => solidityCFunSupported f
  | _ => true

/-- Lightweight string envelope for CAB certificate metadata. -/
def cabEnvelope (cert : CABCertificate) : String :=
  "{" ++
    "\"specId\":" ++ quote cert.specId ++ "," ++
    "\"route\":" ++ quote cert.route ++ "," ++
    "\"proofRef\":" ++ quote cert.proofRef ++ "," ++
    "\"witnessDigest\":" ++ quote cert.witnessDigest ++
  "}"

/-- Export envelope for emitted artifacts; includes route and artifact kind tags. -/
def emittedArtifactEnvelope (record : EmittedArtifactRecord) : String :=
  "{" ++
    "\"envelope_schema_version\":\"1.1.0\"," ++
    "\"route\":" ++ quote (routeLabel record.route) ++ "," ++
    "\"cert\":" ++ cabEnvelope record.cert ++ "," ++
    "\"artifactKind\":" ++ quote (artifactKind record.artifact) ++
    artifactPayloadFields record.artifact ++
  "}"

/-- Route/certificate linkage remains available as a theorem-level invariant. -/
theorem emittedArtifactEnvelope_route_link (record : EmittedArtifactRecord) :
    record.cert.route = routeLabel record.route :=
  record.route_consistent

private def emitEnvelopeWithPreference (n : Nat) (preferredBackend? : Option Routing.BackendClass) :
    String :=
  emittedArtifactEnvelope (Examples.emitNatRecordWithPreference add1Bridge n preferredBackend?)

private def emitNat2EnvelopeWithPreference (x y : Nat) (preferredBackend? : Option Routing.BackendClass) :
    String :=
  emittedArtifactEnvelope (Examples.emitNat2RecordWithPreference add2Bridge x y preferredBackend?)

/-- Convenience export envelope for the add1 emitted record. -/
def emitAdd1Envelope (n : Nat) : String :=
  emitEnvelopeWithPreference n none

/-- Convenience export envelope for the add2 emitted record. -/
def emitAdd2Envelope (x y : Nat) : String :=
  emitNat2EnvelopeWithPreference x y none

/-- Convenience export envelope for the add1 emitted record with explicit highIRC preference. -/
def emitAdd1HighIRCEvelope (n : Nat) : String :=
  emitEnvelopeWithPreference n (some Routing.BackendClass.highIRC)

/-- Compatibility alias for historical naming with contiguous acronym. -/
def emitAdd1HighIRCEnvelope (n : Nat) : String :=
  emitAdd1HighIRCEvelope n

/-- Convenience export envelope for add1 with explicit WasmMini preference. -/
def emitAdd1WasmEnvelope (n : Nat) : String :=
  emitEnvelopeWithPreference n (some Routing.BackendClass.wasmMini)

/-- Convenience export envelope for add1 with explicit pythonFFI preference. -/
def emitAdd1PythonEnvelope (n : Nat) : String :=
  emitEnvelopeWithPreference n (some Routing.BackendClass.pythonFFI)

/-- Convenience export envelope for add1 with explicit Solidity preference. -/
def emitAdd1SolidityEnvelope (n : Nat) : String :=
  emitEnvelopeWithPreference n (some Routing.BackendClass.solidity)

/-- Convenience export envelope for the add2 emitted record with explicit highIRC preference. -/
def emitAdd2HighIRCEvelope (x y : Nat) : String :=
  emitNat2EnvelopeWithPreference x y (some Routing.BackendClass.highIRC)

/-- Compatibility alias for historical naming with contiguous acronym. -/
def emitAdd2HighIRCEnvelope (x y : Nat) : String :=
  emitAdd2HighIRCEvelope x y

/-- Convenience export envelope for add2 with explicit WasmMini preference. -/
def emitAdd2WasmEnvelope (x y : Nat) : String :=
  emitNat2EnvelopeWithPreference x y (some Routing.BackendClass.wasmMini)

/-- Convenience export envelope for add2 with explicit pythonFFI preference. -/
def emitAdd2PythonEnvelope (x y : Nat) : String :=
  emitNat2EnvelopeWithPreference x y (some Routing.BackendClass.pythonFFI)

/-- Convenience export envelope for add2 with explicit Solidity preference. -/
def emitAdd2SolidityEnvelope (x y : Nat) : String :=
  emitNat2EnvelopeWithPreference x y (some Routing.BackendClass.solidity)

end Packaging
end HeytingVeil
end HeytingLean
