import Lean
import Lean.Data.Json

/-!
# HeytingLean.BountyHunter.Solc.ExtractIR

Utilities for extracting the `ir` / `irOptimized` fields from Solidity compiler
**standard JSON** output.

We keep this small and deterministic: no shelling out to `solc`, only parsing an
already-produced JSON file.
-/

namespace HeytingLean.BountyHunter.Solc

open Lean
open Lean.Json

namespace Internal

private def orErr {α} : Option α → String → Except String α
  | some a, _ => .ok a
  | none, msg => .error msg

private def getObjE (j : Json) (ctx : String) : Except String (Std.TreeMap.Raw String Json compare) := do
  match j.getObj? with
  | .ok o => pure o
  | .error _ => .error s!"expected object ({ctx})"

private def getStrE (j : Json) (ctx : String) : Except String String := do
  match j.getStr? with
  | .ok s => pure s
  | .error _ => .error s!"expected string ({ctx})"

private def getArrE (j : Json) (ctx : String) : Except String (Array Json) := do
  match j.getArr? with
  | .ok a => pure a
  | .error _ => .error s!"expected array ({ctx})"

private def getObjValE (obj : Std.TreeMap.Raw String Json compare) (k : String) (ctx : String) :
    Except String Json := do
  orErr (obj.get? k) s!"missing field '{k}' ({ctx})"

private def optStr (j? : Option Json) : String :=
  match j? with
  | none => ""
  | some j =>
      match j.getStr? with
      | .ok s => s
      | .error _ => ""

private def errorsSummaryFromRoot (root : Std.TreeMap.Raw String Json compare) : Array String :=
  match root.get? "errors" with
  | none => #[]
  | some ej =>
      match ej.getArr? with
      | .error _ => #[]
      | .ok errsArr =>
          errsArr.foldl
            (fun acc it =>
              match it.getObj? with
              | .error _ => acc
              | .ok o =>
                  by
                    let fm := optStr (o.get? "formattedMessage")
                    let msg := optStr (o.get? "message")
                    let sev := optStr (o.get? "severity")
                    let text := if fm.isEmpty then msg else fm
                    let sevPrefix := if sev.isEmpty then "" else s!"[{sev}] "
                    exact if text.isEmpty then acc else acc.push (sevPrefix ++ text))
            #[]

end Internal

structure Selector where
  /-- The key under `contracts` for the source unit (often the `.sol` filename). -/
  sourceUnit : String
  /-- The contract name under that source unit. -/
  contractName : String
  /-- Which field to extract (default: `ir`). -/
  field : String := "ir"
  deriving Repr

/-- Extract a string field (e.g. `ir` or `irOptimized`) from solc standard-json output. -/
def extractFieldE (out : Json) (sel : Selector) : Except String String := do
  let root ← Internal.getObjE out "solc output"
  let contractsJ ←
    match root.get? "contracts" with
    | some j => pure j
    | none =>
        let errs := Internal.errorsSummaryFromRoot root
        if errs.isEmpty then
          .error "missing field 'contracts' (solc output)"
        else
          let errText := String.intercalate "\n" errs.toList
          .error s!"missing field 'contracts' (solc output); solc errors:\n{errText}"
  let contracts ← Internal.getObjE contractsJ "contracts"
  let srcJ ← Internal.getObjValE contracts sel.sourceUnit "contracts.<sourceUnit>"
  let srcObj ← Internal.getObjE srcJ s!"contracts.{sel.sourceUnit}"
  let cJ ← Internal.getObjValE srcObj sel.contractName s!"contracts.{sel.sourceUnit}.<contractName>"
  let cObj ← Internal.getObjE cJ s!"contracts.{sel.sourceUnit}.{sel.contractName}"
  let fJ ← Internal.getObjValE cObj sel.field s!"contracts.{sel.sourceUnit}.{sel.contractName}.{sel.field}"
  Internal.getStrE fJ s!"{sel.field}"

private def sortedKeys (obj : Std.TreeMap.Raw String Json compare) : Array String :=
  let ks := obj.toList.map (fun (p : String × Json) => p.1)
  (ks.mergeSort).toArray

def listSourceUnitsE (out : Json) : Except String (Array String) := do
  let root ← Internal.getObjE out "solc output"
  let contractsJ ←
    match root.get? "contracts" with
    | some j => pure j
    | none =>
        let errs := Internal.errorsSummaryFromRoot root
        if errs.isEmpty then
          .error "missing field 'contracts' (solc output)"
        else
          let errText := String.intercalate "\n" errs.toList
          .error s!"missing field 'contracts' (solc output); solc errors:\n{errText}"
  let contracts ← Internal.getObjE contractsJ "contracts"
  pure (sortedKeys contracts)

def listContractNamesE (out : Json) (sourceUnit : String) : Except String (Array String) := do
  let root ← Internal.getObjE out "solc output"
  let contractsJ ←
    match root.get? "contracts" with
    | some j => pure j
    | none =>
        let errs := Internal.errorsSummaryFromRoot root
        if errs.isEmpty then
          .error "missing field 'contracts' (solc output)"
        else
          let errText := String.intercalate "\n" errs.toList
          .error s!"missing field 'contracts' (solc output); solc errors:\n{errText}"
  let contracts ← Internal.getObjE contractsJ "contracts"
  let srcJ ← Internal.getObjValE contracts sourceUnit "contracts.<sourceUnit>"
  let srcObj ← Internal.getObjE srcJ s!"contracts.{sourceUnit}"
  pure (sortedKeys srcObj)

end HeytingLean.BountyHunter.Solc
