import Lean
import Lean.Data.Json
import HeytingLean.Crypto.Form
import HeytingLean.Crypto.FormJson
import HeytingLean.Crypto.Hash.Poseidon
import HeytingLean.Crypto.Trace

open Lean

namespace HeytingLean.CLI
namespace ZKRunner

structure Result where
  mode      : String
  info      : String
  verified  : Bool
  deriving Repr

def resultToJson (r : Result) : Json :=
  Json.mkObj [
    ("mode", Json.str r.mode),
    ("info", Json.str r.info),
    ("verified", Json.bool r.verified)
  ]

def fileExists (p : System.FilePath) : IO Bool := do
  try return (← p.pathExists) catch _ => return false

private def ensurePublicJson : IO System.FilePath := do
  -- Priority: LOF_PUBLIC_PATH > (derive from LOF_FORM_PATH) > default sample
  match (← IO.getEnv "LOF_PUBLIC_PATH") with
  | some p => return System.FilePath.mk p
  | none =>
    match (← IO.getEnv "LOF_FORM_PATH") with
    | some p =>
      let fp := System.FilePath.mk p
      -- read and parse form
      let content? ← (do
        try
          if ← fp.pathExists then return some (← IO.FS.readFile fp) else return none
        catch _ => return none)
      match content? with
      | some s =>
        match Json.parse s with
        | .ok j =>
          -- compute canonical JSON encoding (we allow j to already be in the expected shape)
          let canonStr := j.compress
          -- If a compact form encoding is provided, prefer it as the Poseidon payload.
          let payloadForCommit ← do
            match (← IO.getEnv "LOF_FORM_ENC_PATH") with
            | some p =>
                let fp := System.FilePath.mk p
                try
                  if ← fp.pathExists then
                    pure (← IO.FS.readFile fp)
                  else
                    pure canonStr
                catch _ => pure canonStr
            | none => pure canonStr
          let commit ← HeytingLean.Crypto.Hash.commitFormIO payloadForCommit
          -- Gather other fields from env or defaults
          let init := (← IO.getEnv "LOF_INITIAL_STATE").getD "init0"
          let finDefault  := (← IO.getEnv "LOF_FINAL_STATE").getD "final0"
          let lensDefault := (← IO.getEnv "LOF_LENS_SEL").getD "0"
          -- Optional strong-trace profile: if LOF_STRONG_TRACE=1 and LOF_TRACE_PATH is set,
          -- derive the trace digest in Lean and set lens/final accordingly.
          let strong := (← IO.getEnv "LOF_STRONG_TRACE").getD "0" == "1"
          let (lens, fin) ← do
            if strong then
              match (← IO.getEnv "LOF_TRACE_PATH") with
              | some p =>
                let tfp := System.FilePath.mk p
                let content? ← (do
                  try
                    if ← tfp.pathExists then return some (← IO.FS.readFile tfp) else return none
                  catch _ => return none)
                match content? with
                | some s =>
                    match Json.parse s with
                    | .ok j =>
                        match HeytingLean.Crypto.Trace.parseOpsJson j with
                        | some ops =>
                            let d := HeytingLean.Crypto.Trace.digestOps ops
                            let lens := toString d
                            let fin :=
                              match String.toNat? init with
                              | some n => toString (n + d)
                              | none => finDefault
                            pure (lens, fin)
                        | none => pure (lensDefault, finDefault)
                    | .error _ => pure (lensDefault, finDefault)
                | none => pure (lensDefault, finDefault)
              | none => pure (lensDefault, finDefault)
            else
              pure (lensDefault, finDefault)
          let outJ := Json.mkObj [
            ("form_commitment", Json.str commit),
            ("initial_state", Json.str init),
            ("final_state", Json.str fin),
            ("lens_selector", Json.str lens)
          ]
          let outDir := System.FilePath.mk ".tmp/zk_runner"
          (do IO.FS.createDirAll outDir) |> (fun _ => pure ())
          let outPath := outDir / "public.json"
          IO.FS.writeFile outPath outJ.compress
          return outPath
        | .error _ =>
          return System.FilePath.mk "../Docs/Examples/public_sample.json"
      | none => return System.FilePath.mk "../Docs/Examples/public_sample.json"
    | none => return System.FilePath.mk "../Docs/Examples/public_sample.json"

def runExternal? (binDir : System.FilePath) : IO (Option Result) := do
  let setupBin := binDir / "lof_setup"
  let proverBin := binDir / "lof_prover"
  let verifyBin := binDir / "lof_verify"
  if !(← fileExists setupBin) || !(← fileExists proverBin) || !(← fileExists verifyBin) then
    return none
  let cwd ← IO.currentDir
  let workRel := System.FilePath.mk ".tmp/zk_runner"
  let work := cwd / workRel
  (do IO.FS.createDirAll work) |> (fun _ => pure ())
  let pk := work / "pk.bin"
  let vk := work / "vk.bin"
  let proof := work / "proof.bin"
  let pubPath ← ensurePublicJson
  -- Debug: show paths
  let dbg := s!"paths: binDir={binDir}, cwd={cwd}, pk={pk}, vk={vk}, proof={proof}, pub={pubPath}"
  -- Run setup
  let setupOut ← IO.Process.output {
    cmd := setupBin.toString,
    args := #[pk.toString, vk.toString],
    cwd := none
  }
  -- Prover: prefer explicit external witness if provided; otherwise optional form-derived witness
  let passWitness := (← IO.getEnv "LOF_PROVER_FORM_WITNESS").getD "0" == "1"
  -- If passing a form-derived witness, derive a canonical payload file to provide to the prover
  let canonFile? ← do
    if passWitness then
      match (← IO.getEnv "LOF_FORM_PATH") with
      | some s =>
          let fp := System.FilePath.mk s
          let content? ← (do
            try
              if ← fp.pathExists then return some (← IO.FS.readFile fp) else return none
            catch _ => return none)
          match content? with
          | some txt =>
              match Json.parse txt with
              | .ok j =>
                  let canonStr := j.compress
                  let out := work / "canon.txt"
                  IO.FS.writeFile out canonStr
                  pure (some out)
              | .error _ => pure none
          | none => pure none
      | none => pure none
    else
      pure none
  let proverArgs ← do
    let mut args := #[pk.toString, pubPath.toString, proof.toString]
    -- explicit external witness
    match (← IO.getEnv "LOF_PROVER_WITNESS_PATH") with
    | some w => args := args ++ #["--witness", w]
    | none =>
        if passWitness then
          match canonFile? with
          | some path => args := args ++ #["--form", path.toString]
          | none      => pure ()
        else
          pure ()
    -- optional form encoding path (compact encoding)
    match (← IO.getEnv "LOF_FORM_ENC_PATH") with
    | some p => args := args ++ #["--form-enc", p]
    | none => pure ()
    -- optional external trace witness (digest) or trace ops (derive digest)
    match (← IO.getEnv "LOF_PROVER_TRACE_PATH") with
    | some t => args := args ++ #["--trace", t]
    | none => pure ()
    match (← IO.getEnv "LOF_TRACE_PATH") with
    | some t => args := args ++ #["--trace-ops", t]
    | none => pure ()
    pure args
  let proverOut ← IO.Process.output {
    cmd := proverBin.toString,
    args := proverArgs,
    cwd := none
  }
  -- Verify
  let verifyOut ← IO.Process.output {
    cmd := verifyBin.toString,
    args := #[vk.toString, pubPath.toString, proof.toString],
    cwd := none
  }
  let infoStr := String.intercalate ";" [
      dbg,
      s!"setup(code={setupOut.exitCode}):{setupOut.stdout}{setupOut.stderr}",
      s!"prover(code={proverOut.exitCode}):{proverOut.stdout}{proverOut.stderr}",
      s!"verify(code={verifyOut.exitCode}):{verifyOut.stdout}{verifyOut.stderr}"
    ]
  return some { mode := "external", info := infoStr, verified := verifyOut.exitCode == 0 }

def run : IO Unit := do
  match (← IO.getEnv "LOF_RUST_BIN_DIR") with
  | some dir =>
      match (← runExternal? (System.FilePath.mk dir)) with
      | some r => IO.println (resultToJson r |>.compress)
      | none =>
          let fallback : Json := Json.mkObj [("mode", Json.str "fallback"), ("info", Json.str "binaries not found"), ("verified", Json.bool false)]
          IO.println fallback.compress
  | none =>
      let fallback : Json := Json.mkObj [("mode", Json.str "fallback"), ("info", Json.str "no bin dir"), ("verified", Json.bool false)]
      IO.println fallback.compress

end ZKRunner
end HeytingLean.CLI

def main : IO Unit := HeytingLean.CLI.ZKRunner.run
