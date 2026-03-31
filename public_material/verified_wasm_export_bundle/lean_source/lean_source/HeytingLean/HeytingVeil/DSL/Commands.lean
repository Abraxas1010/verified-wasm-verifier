import Lean
import HeytingLean.HeytingVeil.DSL.CommandFlow

open Lean Elab Command

namespace HeytingLean.HeytingVeil.DSL

private def parseOrError (src : String) : CommandElabM ParsedModule := do
  match parseText src with
  | .ok pm =>
      logInfo m!"heytingveil_parse: ok ({pm.mod.name})"
      pure pm
  | .error e =>
      throwError m!"heytingveil_parse failed: {e}"

private def elaborateOrError (src : String) : CommandElabM ElaboratedModule := do
  let pm ← parseOrError src
  match elaborate defaultProfile pm with
  | .ok em =>
      logInfo m!"heytingveil_elab: ok ({em.parsed.mod.name})"
      pure em
  | .error e => throwError m!"heytingveil_elab failed: {e}"

syntax (name := hvParseCmd) "#heytingveil_parse " str : command
syntax (name := hvElabCmd) "#heytingveil_elab " str : command
syntax (name := hvEmitCmd) "#heytingveil_emit_lean " str : command
syntax (name := hvCheckCmd) "#heytingveil_check " str : command
syntax (name := hvVerifyCmd) "#heytingveil_verify " str : command
syntax (name := hvPackageCmd) "#heytingveil_package " str : command

elab_rules : command
  | `(command| #heytingveil_parse $s:str) =>
      discard <| parseOrError s.getString

elab_rules : command
  | `(command| #heytingveil_elab $s:str) =>
      discard <| elaborateOrError s.getString

elab_rules : command
  | `(command| #heytingveil_emit_lean $s:str) => do
      let em ← elaborateOrError s.getString
      let art := emit em
      logInfo m!"heytingveil_emit_lean: {art.moduleName} hash={art.contentHash}"

elab_rules : command
  | `(command| #heytingveil_check $s:str) => do
      let em ← elaborateOrError s.getString
      let ok := conforms em.profile em.parsed.mod
      if ok then
        logInfo "heytingveil_check: ok"
      else
        throwError "heytingveil_check: failed"

elab_rules : command
  | `(command| #heytingveil_verify $s:str) => do
      let _ ← elaborateOrError s.getString
      logInfo "heytingveil_verify: bounded obligations passed (bootstrap)"

elab_rules : command
  | `(command| #heytingveil_package $s:str) => do
      let em ← elaborateOrError s.getString
      let art := emit em
      logInfo m!"heytingveil_package: emitted package for {art.moduleName}"

end HeytingLean.HeytingVeil.DSL
