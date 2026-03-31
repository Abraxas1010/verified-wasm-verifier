import HeytingLean.LoF.CryptoSheaf.Quantum.ContextualitySite
import HeytingLean.LoF.CryptoSheaf.Quantum.EmpiricalModel
import HeytingLean.LoF.CryptoSheaf.Quantum.Examples.ValuationBool

namespace HeytingLean
namespace CLI

open HeytingLean.LoF.CryptoSheaf.Quantum.Examples

def CryptoSheafDemoContext.main : IO Unit := do
  -- Compute locals/glue via the Nat companion consistent with the certified valuation.
  let lTrue  : Nat := boolValuationNat True
  let lFalse : Nat := boolValuationNat False
  let glue   : Nat := boolValuationNat False -- miniature cover glue = False
  -- Check a tiny inequality at the Nat layer (mirrors ℝ-theorem `boolValuation_bound`).
  let boundOk : Bool := Nat.ble glue (Nat.min lTrue lFalse)
  let payload := "{" ++
    "\"contextual\":true," ++
    "\"cover_size\":2," ++
    "\"valuation\":{\"locals\":[" ++ toString lTrue ++ "," ++ toString lFalse ++ "],\"glue\":" ++ toString glue ++ ",\"bound_satisfied\":" ++ toString boundOk ++ "}}"
  IO.println payload

end CLI
end HeytingLean

def main (_argv : List String) : IO Unit := HeytingLean.CLI.CryptoSheafDemoContext.main
