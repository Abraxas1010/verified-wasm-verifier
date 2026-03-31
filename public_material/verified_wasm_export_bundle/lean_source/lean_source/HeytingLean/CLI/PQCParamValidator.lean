import HeytingLean.Crypto.KEM.MLKEM203Params
import HeytingLean.Crypto.KEM.MLKEMFailureBounds
import HeytingLean.Crypto.KEM.MLKEMParamSearch
import HeytingLean.Crypto.Lattice.NTT
import Lean.Data.Json

/-!
# PQC Parameter Validator (FIPS 203)

This executable prints a JSON report describing the ML-KEM parameter sets from NIST FIPS 203
and runs a small set of internal consistency checks:

- the parameter bundle satisfies a decidable validity predicate (`validParams`);
- the standard NTT root `ζ = 17` satisfies the basic `2^8` power facts mod `q = 3329`.

This tool does **not** claim IND-CCA security or failure-probability bounds as proven facts.
Instead it reports the standard (externally justified) failure bound strings used by the spec
and keeps the cryptographic reductions in the conjecture/proof pipeline.
-/

namespace HeytingLean
namespace CLI

open HeytingLean.Crypto.KEM.FIPS203

namespace PQCValidator

structure ValidationReport where
  paramSet : String
  valid : Bool
  n : Nat
  q : Nat
  k : Nat
  eta1 : Nat
  eta2 : Nat
  du : Nat
  dv : Nat
  ekSize : Nat
  dkSize : Nat
  ctSize : Nat
  failureProbBound : String
  securityLevel : String
  nttRootOk : Bool
  deriving Repr

private def securityLevelString (p : MLKEM203Params) : String :=
  match p.k with
  | 2 => "NIST Level 1 (128-bit)"
  | 3 => "NIST Level 3 (192-bit)"
  | 4 => "NIST Level 5 (256-bit)"
  | _ => "unknown"

def validateParams (p : MLKEM203Params) : ValidationReport :=
  { paramSet := p.name
  , valid := decide (validParams p)
  , n := p.n
  , q := p.q
  , k := p.k
  , eta1 := p.eta1
  , eta2 := p.eta2
  , du := p.du
  , dv := p.dv
  , ekSize := p.ekSize
  , dkSize := p.dkSize
  , ctSize := p.ctSize
  , failureProbBound := reportedFailureBoundString p
  , securityLevel := securityLevelString p
  , nttRootOk := decide (HeytingLean.Crypto.Lattice.NTT.primitive256)
  }

def toJson (r : ValidationReport) : Lean.Json :=
  Lean.Json.mkObj
    [ ("paramSet", Lean.Json.str r.paramSet)
    , ("valid", Lean.Json.bool r.valid)
    , ("n", Lean.Json.num (Lean.JsonNumber.fromNat r.n))
    , ("q", Lean.Json.num (Lean.JsonNumber.fromNat r.q))
    , ("k", Lean.Json.num (Lean.JsonNumber.fromNat r.k))
    , ("eta1", Lean.Json.num (Lean.JsonNumber.fromNat r.eta1))
    , ("eta2", Lean.Json.num (Lean.JsonNumber.fromNat r.eta2))
    , ("du", Lean.Json.num (Lean.JsonNumber.fromNat r.du))
    , ("dv", Lean.Json.num (Lean.JsonNumber.fromNat r.dv))
    , ("ekSize", Lean.Json.num (Lean.JsonNumber.fromNat r.ekSize))
    , ("dkSize", Lean.Json.num (Lean.JsonNumber.fromNat r.dkSize))
    , ("ctSize", Lean.Json.num (Lean.JsonNumber.fromNat r.ctSize))
    , ("failureProbBound", Lean.Json.str r.failureProbBound)
    , ("securityLevel", Lean.Json.str r.securityLevel)
    , ("nttRootOk", Lean.Json.bool r.nttRootOk)
    ]

def reportJson : Lean.Json :=
  Lean.Json.arr <| HeytingLean.Crypto.KEM.FIPS203.all.map fun p => toJson (validateParams p)

private def getFlagValue? (flag : String) (args : List String) : Option String :=
  let rec go : List String → Option String
    | [] => none
    | x :: y :: xs => if x == flag then some y else go (y :: xs)
    | _ :: [] => none
  go args

private def hasFlag (flag : String) (args : List String) : Bool :=
  args.any (fun x => x == flag)

private def parseSecurityLevel? (s : String) : Option HeytingLean.Crypto.KEM.FIPS203.SecurityLevel :=
  match s.trim.toLower with
  | "cat1" => some .cat1
  | "cat3" => some .cat3
  | "cat5" => some .cat5
  | _ => none

private def securityLevelToString (l : HeytingLean.Crypto.KEM.FIPS203.SecurityLevel) : String :=
  match l with
  | .cat1 => "cat1"
  | .cat3 => "cat3"
  | .cat5 => "cat5"

private def suggestionJson (level : HeytingLean.Crypto.KEM.FIPS203.SecurityLevel) (maxCt : Nat) : Lean.Json :=
  let sug := HeytingLean.Crypto.KEM.FIPS203.suggestParams level maxCt
  let sugJson :=
    match sug with
    | some p => Lean.Json.str p.name
    | none => Lean.Json.null
  Lean.Json.mkObj
    [ ("mode", Lean.Json.str "suggest")
    , ("level", Lean.Json.str (securityLevelToString level))
    , ("maxCtSize", Lean.Json.num (Lean.JsonNumber.fromNat maxCt))
    , ("suggested", sugJson)
    ]

def main (argv : List String) : IO Unit := do
  if hasFlag "--help" argv then
    IO.println "usage: pqc_param_validator [--suggest cat1|cat3|cat5 --max-ct <nat>]"
    return
  if hasFlag "--suggest" argv then
    let levelStr := (getFlagValue? "--suggest" argv).getD ""
    let level? := parseSecurityLevel? levelStr
    match level? with
    | none =>
        IO.eprintln s!"unknown security level: {levelStr}"
        return
    | some level =>
        let maxCtStr := getFlagValue? "--max-ct" argv
        let maxCt := maxCtStr.bind String.toNat? |>.getD 1000000000
        IO.println (toString (suggestionJson level maxCt))
        return
  IO.println (toString reportJson)

end PQCValidator

end CLI
end HeytingLean

-- Intentionally no top-level `main` here: this module is imported by other executables.
