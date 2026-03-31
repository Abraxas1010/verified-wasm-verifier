import HeytingLean.Crypto.KEM.MLKEM203Params
import HeytingLean.Crypto.KEM.MLKEMFailureModel
import Lean.Data.Json

/-!
# PQC Failure Bound Explorer (Gap 3 helper)

This executable computes **windowed tail upper bounds** for simplified ML-KEM-style residual terms,
using the `WindowedCounts` machinery from `HeytingLean.Crypto.KEM.MLKEMFailureModel`.

It is intended for **interactive exploration** and for producing WIP artifacts. It is *not* a
formal replacement for the NIST failure-probability axioms yet.
-/

namespace HeytingLean
namespace CLI

open HeytingLean.Crypto.KEM.FIPS203
open HeytingLean.Crypto.KEM.FIPS203.FailureModel

namespace PQCFailureBound

private def hasFlag (flag : String) (args : List String) : Bool :=
  args.any (fun x => x == flag)

private def getFlagValue? (flag : String) (args : List String) : Option String :=
  let rec go : List String → Option String
    | [] => none
    | x :: y :: xs => if x == flag then some y else go (y :: xs)
    | _ :: [] => none
  go args

private def parsePreset? (s : String) : Option MLKEM203Params :=
  match s.trim.toLower with
  | "mlkem512" => some mlkem512
  | "mlkem768" => some mlkem768
  | "mlkem1024" => some mlkem1024
  | _ => none

private def natOr (s : Option String) (dflt : Nat) : Nat :=
  s.bind String.toNat? |>.getD dflt

private def pow2 (k : Nat) : Nat := 2 ^ k

private def bitLen (x : Nat) : Nat :=
  if x = 0 then 0 else Nat.log2 x + 1

private def reportJson (p : MLKEM203Params) (terms threshold kTarget : Nat) : Lean.Json :=
  let overflow := sumOfCBDProducts_tailUB p.eta1 p.eta2 terms threshold
  let expBits := terms * (2 * p.eta1 + 2 * p.eta2)
  let ubBits := bitLen overflow
  let slackBits := expBits - ubBits
  let okTarget := overflow * pow2 kTarget ≤ pow2 expBits
  let okUnion256 := overflow * 256 * pow2 kTarget ≤ pow2 expBits
  Lean.Json.mkObj
    [ ("preset", Lean.Json.str p.name)
    , ("k", Lean.Json.num (Lean.JsonNumber.fromNat p.k))
    , ("n", Lean.Json.num (Lean.JsonNumber.fromNat p.n))
    , ("eta1", Lean.Json.num (Lean.JsonNumber.fromNat p.eta1))
    , ("eta2", Lean.Json.num (Lean.JsonNumber.fromNat p.eta2))
    , ("terms", Lean.Json.num (Lean.JsonNumber.fromNat terms))
    , ("threshold", Lean.Json.num (Lean.JsonNumber.fromNat threshold))
    , ("overflowCountUB", Lean.Json.num (Lean.JsonNumber.fromNat overflow))
    , ("expBitsTotal", Lean.Json.num (Lean.JsonNumber.fromNat expBits))
    , ("overflowBitLen", Lean.Json.num (Lean.JsonNumber.fromNat ubBits))
    , ("slackBits", Lean.Json.num (Lean.JsonNumber.fromNat slackBits))
    , ("targetK", Lean.Json.num (Lean.JsonNumber.fromNat kTarget))
    , ("boundOkSingle", Lean.Json.bool okTarget)
    , ("boundOkUnion256", Lean.Json.bool okUnion256)
    ]

def main (argv : List String) : IO Unit := do
  if argv.isEmpty || hasFlag "--help" argv then
    IO.println "usage: pqc_failure_bound --preset mlkem512|mlkem768|mlkem1024 [--terms N] [--full] [--threshold T] [--k 80]"
    IO.println "  default: computes a small run unless --full is provided"
    return
  let presetStr := (getFlagValue? "--preset" argv).getD ""
  let p? := parsePreset? presetStr
  let some p := p? | do
    IO.eprintln s!"unknown --preset: {presetStr}"
    return
  let threshold := natOr (getFlagValue? "--threshold" argv) (3329 / 4)
  let kTarget := natOr (getFlagValue? "--k" argv) 80
  let termsDefault := if hasFlag "--full" argv then p.k * p.n else 64
  let terms := natOr (getFlagValue? "--terms" argv) termsDefault
  IO.println (toString (reportJson p terms threshold kTarget))

end PQCFailureBound

end CLI
end HeytingLean

-- Intentionally no top-level `main` here: this module is imported by other executables.
