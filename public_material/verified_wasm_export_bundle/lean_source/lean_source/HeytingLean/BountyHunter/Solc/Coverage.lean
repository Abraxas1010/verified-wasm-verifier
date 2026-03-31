import Lean
import Lean.Data.Json
import Std
import HeytingLean.BountyHunter.Solc.YulObjectMini
import HeytingLean.BountyHunter.Solc.YulTextMini

/-!
# HeytingLean.BountyHunter.Solc.Coverage

Coverage instrumentation for solc `ir` / `irOptimized` ingestion.

We do **not** guess: coverage reports are intended to drive incremental parser work.
-/

namespace HeytingLean.BountyHunter.Solc

open Lean

structure CoverageFailure where
  loc : String
  error : String
  deriving Repr, Inhabited

structure CoverageReport where
  version : String := "bh.solc_coverage.v0"
  yulObjectOk : Bool := false
  codeBlocksTotal : Nat := 0
  codeBlocksParsed : Nat := 0
  functionsTotal : Nat := 0
  functionsParsed : Nat := 0
  failures : Array CoverageFailure := #[]
  deriving Repr, Inhabited

def coverageFailureToJson (f : CoverageFailure) : Json :=
  Json.mkObj [("loc", Json.str f.loc), ("error", Json.str f.error)]

def coverageReportToJson (r : CoverageReport) : Json :=
  Json.mkObj
    [ ("version", Json.str r.version)
    , ("yulObjectOk", Json.bool r.yulObjectOk)
    , ("codeBlocksTotal", Json.num r.codeBlocksTotal)
    , ("codeBlocksParsed", Json.num r.codeBlocksParsed)
    , ("functionsTotal", Json.num r.functionsTotal)
    , ("functionsParsed", Json.num r.functionsParsed)
    , ("failures", Json.arr (r.failures.map coverageFailureToJson))
    ]

private def bumpFailure (r : CoverageReport) (loc err : String) : CoverageReport :=
  { r with failures := r.failures.push { loc := loc, error := err } }

private partial def analyzeCodeBlock (path : String) (code : String) (r0 : CoverageReport) : CoverageReport :=
  Id.run do
    let mut r := { r0 with codeBlocksTotal := r0.codeBlocksTotal + 1 }
    let namesE := HeytingLean.BountyHunter.Solc.YulTextMini.listFunctionNamesE code
    match namesE with
    | .error e =>
        r := bumpFailure r s!"{path}.code" s!"listFunctionNamesE: {e}"
        return r
    | .ok names =>
        r := { r with codeBlocksParsed := r.codeBlocksParsed + 1 }
        for fn in names do
          r := { r with functionsTotal := r.functionsTotal + 1 }
          match HeytingLean.BountyHunter.Solc.YulTextMini.parseFunctionBodyE code fn with
          | .ok _ =>
              r := { r with functionsParsed := r.functionsParsed + 1 }
          | .error e =>
              r := bumpFailure r s!"{path}.function[{fn}]" e
        return r

private partial def analyzeItem (path : String) (it : HeytingLean.BountyHunter.Solc.YulObjectMini.Item)
    (r0 : CoverageReport) : CoverageReport :=
  match it with
  | .data _ _ => r0
  | .code body => analyzeCodeBlock path body r0
  | .object name items =>
      items.foldl (fun r it => analyzeItem (path ++ s!"/object[{name}]") it r) r0

def analyzeE (ir : String) : CoverageReport :=
  match HeytingLean.BountyHunter.Solc.YulObjectMini.parseProgramE ir with
  | .error e =>
      bumpFailure {} "yulObject" e
  | .ok prog =>
      let r0 : CoverageReport := { yulObjectOk := true }
      prog.items.foldl (fun r it => analyzeItem "root" it r) r0

end HeytingLean.BountyHunter.Solc
