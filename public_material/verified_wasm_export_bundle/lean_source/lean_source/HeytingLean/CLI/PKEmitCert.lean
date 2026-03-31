import Lean
import Lean.Data.Json
import HeytingLean.CLI.Args
import HeytingLean.Util.SHA

/-!
Emit a proof-kit compatible certificate (cert_pk.json) using our local artifacts.
Reads public.json and r1cs.json from an output directory and writes cert_pk.json
conforming to proof-kit's certificate.schema.json shape.

Layout:
{
  "inputs": [ {"k":"IRv","v":"v1"}, ... ],
  "omega": { "meta": { "output_index": N, "env_indices": [...] } },
  "rewrites": [],
  "digests": { "omega": "0x...", "stmt": "0x..." },
  "commitments": { "policyCommitment": "0x..64", "stateCommit_pre": "0x..64", "stateCommit_post": "0x..64", "nullifier": "0x..64" },
  "blueprint_hash": "0x..."
}
-/

namespace HeytingLean
namespace CLI
namespace PKEmitCert

open Lean

private def readFileE (p : System.FilePath) : IO (Except String String) := do
  try let s ← IO.FS.readFile p; pure (.ok s) catch e => pure (.error s!"read error at {p}: {e}")

def getStr (j : Json) (k : String) (default := "") : String :=
  match j.getObjVal? k with
  | .ok (.str s) => s
  | _ => default

def main (args : List String) : IO UInt32 := do
  let args := HeytingLean.CLI.stripLakeArgs args
  match args with
  | [outDirStr] =>
      let outDir := System.FilePath.mk outDirStr
      let pubPath := outDir / "public.json"
      let r1csPath := outDir / "r1cs.json"
      let pubRaw ← match (← readFileE pubPath) with | .ok s => pure s | .error m => IO.eprintln m; return 1
      let r1csRaw ← match (← readFileE r1csPath) with | .ok s => pure s | .error m => IO.eprintln m; return 1
      let pubJ ← match Json.parse pubRaw with | .ok j => pure j | .error e => IO.eprintln e; return 1
      -- inputs
      let inputsArr : Array Json := #[(Json.mkObj [("k", Json.str "IRv"), ("v", Json.str (getStr pubJ "IRv"))])
        , (Json.mkObj [("k", Json.str "rewriteTablev"), ("v", Json.str (getStr pubJ "rewriteTablev"))])
        , (Json.mkObj [("k", Json.str "canonv"), ("v", Json.str (getStr pubJ "canonv"))])
        , (Json.mkObj [("k", Json.str "circuitv"), ("v", Json.str (getStr pubJ "circuitv"))])
        , (Json.mkObj [("k", Json.str "chainId"), ("v", Json.str (getStr pubJ "chainId"))])
        ]
      -- omega/meta
      let outIdx := match (pubJ.getObjVal? "output_index") with | .ok v => (match v.getNat? with | .ok n => n | .error _ => 0) | _ => 0
      let envIdxs : Array Json := match pubJ.getObjVal? "env_indices" with
        | .ok (.arr a) => a
        | _ => #[]
      let omega := Json.mkObj [ ("meta", Json.mkObj [ ("output_index", Json.num outIdx)
                                                     , ("env_indices", Json.arr envIdxs) ]) ]
      -- digests
      let omegaDigest := (← HeytingLean.Util.sha256HexOfStringIO r1csRaw)
      let omegaDigestHex := if omegaDigest.startsWith "0x" then omegaDigest else s!"0x{omegaDigest}"
      let stmtDigest := getStr pubJ "omega_digest_public"
      let stmtDigestHex := if stmtDigest.startsWith "0x" then stmtDigest else s!"0x{stmtDigest}"
      let digests := Json.mkObj [ ("omega", Json.str omegaDigestHex), ("stmt", Json.str stmtDigestHex) ]
      -- commitments from public
      let commitments := Json.mkObj
        [ ("policyCommitment", Json.str (getStr pubJ "policyCommitment"))
        , ("stateCommit_pre", Json.str (getStr pubJ "stateCommit_pre"))
        , ("stateCommit_post", Json.str (getStr pubJ "stateCommit_post"))
        , ("nullifier", Json.str (getStr pubJ "nullifier")) ]
      let rewrites : Json := Json.arr #[]
      let blueprintHash := omegaDigestHex
      let cert := Json.mkObj
        [ ("inputs", Json.arr inputsArr)
        , ("omega", omega)
        , ("rewrites", rewrites)
        , ("digests", digests)
        , ("commitments", commitments)
        , ("blueprint_hash", Json.str blueprintHash)
        ]
      let outPath := outDir / "cert_pk.json"
      IO.FS.writeFile outPath (cert.compress)
      IO.println s!"wrote {outPath}"
      return 0
  | _ =>
      IO.eprintln "usage: lake exe pk_emit_cert <outdir>"; return 2

end PKEmitCert
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.PKEmitCert.main args
