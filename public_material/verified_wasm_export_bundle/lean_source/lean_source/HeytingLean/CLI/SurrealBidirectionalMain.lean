import Lean
import Lean.Data.Json
import HeytingLean.CLI.Certified.Json
import HeytingLean.Numbers.Surreal.BidirectionalProof

/-!
# Surreal bidirectional proof demo CLI

This executable is a small, self-contained demonstration of the
forward/backward evidence protocol implemented in:

`HeytingLean.Numbers.Surreal.BidirectionalProof`.

## Modes

- No args: run an internal selftest and print `PASS`.
- `--stdin` / `--input <file>`: read JSON with a `program` field and
  emit `{ forward, verify }` JSON to stdout.

The JSON protocol is intentionally minimal and local-only.
-/

namespace HeytingLean.CLI.SurrealBidirectionalMain

open Lean
open HeytingLean.CLI.Certified
open HeytingLean.Numbers.Surreal
open HeytingLean.Numbers.Surreal.LoFProgram
open HeytingLean.Numbers.Surreal.BidirectionalProof

private def findValue? (flag : String) : List String → Option String
  | [] => none
  | x :: xs =>
      match xs with
      | [] => none
      | y :: _ =>
          if x == flag then some y else findValue? flag xs

private def verifyQueryOfJson (j : Json) : VerifyQuery :=
  let expected := getString? j "expectedRootDigest"
  let maxBirth := getNat? j "maxBirth"
  { expectedRootDigest := expected, maxBirth := maxBirth }

private def selftest : IO UInt32 := do
  -- Build the dyadic 1/2 as a pre-game, compile to a LoF program, run forward, then verify.
  let g := LoFProgram.dyadicPreGame 1 1
  let p ←
    match LoFProgram.Compile.compileChecked g with
    | .ok p => pure p
    | .error e =>
        IO.eprintln s!"E: compileChecked failed: {e}"
        return 1
  match BidirectionalProof.forward p with
  | .error e =>
      IO.eprintln s!"E: forward failed: {e}"
      pure 1
  | .ok forward => do
      let report := BidirectionalProof.verify forward {}
      if !report.ok then
        IO.eprintln s!"E: verify failed: {report.errors}"
        pure 1
      else
        -- Negative tests: basic tamper-evidence checks.
        let badRoot := { forward with rootDigest := "bogus" }
        if (BidirectionalProof.verify badRoot {}).ok then
          IO.eprintln "E: expected rootDigest tamper to fail"
          return 1

        let badToken :=
          { forward with forwardToken := { alg := forward.forwardToken.alg, digest := "bogus" } }
        if (BidirectionalProof.verify badToken {}).ok then
          IO.eprintln "E: expected forwardToken tamper to fail"
          return 1

        match forward.steps[0]? with
        | none => pure ()
        | some s0 =>
            let stepsBad := forward.steps.set! 0 { s0 with nodeDigest := "bogus" }
            let badStep := { forward with steps := stepsBad }
            if (BidirectionalProof.verify badStep {}).ok then
              IO.eprintln "E: expected step tamper to fail"
              return 1

        let badLens :=
          { forward with
              lensPath :=
                [ LensPoint.default
                , { sem := .dialectica, comp := .functional, alg := .tensor } ] }
        if (BidirectionalProof.verify badLens {}).ok then
          IO.eprintln "E: expected lensPath tamper to fail"
          return 1

        -- Dialectica-style: witness + challenge + response.
        let w : DialecticaWitness := { forward := forward }
        let c : DialecticaChallenge := { query := { expectedRootDigest := some forward.rootDigest } }
        let resp := dialecticaRespond w c
        if !resp.ok then
          IO.eprintln s!"E: dialecticaRespond failed: {resp.errors}"
          pure 1
        else
          -- Sheaf-style gluing: two identical witnesses must glue.
          let w2 : DialecticaWitness := { forward := forward }
          match glueWitnesses [w, w2] with
          | .error e =>
              IO.eprintln s!"E: glueWitnesses failed: {e}"
              pure 1
          | .ok _ =>
              IO.println "PASS"
              pure 0

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    return (← selftest)

  let inputE ← readInputJson args
  match inputE with
  | .error e => die s!"E: {e}"
  | .ok jIn =>
      match jIn.getObjVal? "program" with
      | .error _ => die "E: expected JSON object with key 'program'"
      | .ok progJ =>
          match BidirectionalProof.programOfJson progJ with
          | .error e => die s!"E: program parse failed: {e}"
          | .ok program =>
              let q :=
                match jIn.getObjVal? "query" with
                | .ok qj => verifyQueryOfJson qj
                | .error _ => {}
              let maxBirth := q.maxBirth
              let forwardE := BidirectionalProof.forward program BidirectionalProof.defaultLensPath maxBirth
              match forwardE with
              | .error e => die s!"E: forward failed: {e}"
              | .ok forward =>
                  let report := BidirectionalProof.verify forward q
                  let out :=
                    Json.mkObj
                      [ ("forward", forward.toJson)
                      , ("verify", toJson report)
                      ]
                  -- Optional `--out <file>` writes the same JSON to disk.
                  match findValue? "--out" args with
                  | none => okJson out
                  | some path =>
                      try
                        IO.FS.writeFile path out.pretty
                        okJson out
                      catch e =>
                        die s!"E: write failed: {e}"

end HeytingLean.CLI.SurrealBidirectionalMain

open HeytingLean.CLI.SurrealBidirectionalMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.SurrealBidirectionalMain.main args
