import Lean
import HeytingLean.DeFi.Model
import HeytingLean.DeFi.AMM

/-
# defi_demo CLI

Tiny CLI that exercises the DeFi models by constructing simple AMM and
lending states, performing a sample swap using the concrete
constant-product AMM with fees, and printing summaries including a
constant-product invariant check.
-/

namespace HeytingLean
namespace CLI
namespace DeFiDemo

open HeytingLean.DeFi

/-- Sample AMM fee parameters used by the demo. Here we take a fee of
    zero to keep the numbers small while still exercising the concrete
    swap formulas. -/
def sampleParams : AMM.Params :=
  { fee := 0
    fee_nonneg := by decide
    fee_lt_one := by decide }

def main (_argv : List String) : IO UInt32 := do
  -- Initial AMM state and invariant.
  let amm0 : AMM.State := { x := 10, y := 20 }
  let k0 := AMM.k amm0
  let dx : ℚ := 1
  -- Perform an X→Y swap using the concrete AMM model.
  let amm1 := AMM.swapX sampleParams amm0 dx
  let k1 := AMM.k amm1
  let dy := AMM.amountOutX sampleParams amm0 dx
  IO.println s!"defi_demo: initial AMM x={amm0.x}, y={amm0.y}, k={k0}"
  IO.println s!"  swapX Δx={dx}, fee={sampleParams.fee} → x'={amm1.x}, y'={amm1.y}, k'={k1}, Δy_out={dy}"
  IO.println s!"  constant product preserved? {decide (k0 = k1)}"
  -- Minimal lending state summary.
  let lend : Lending.State :=
    { deposits := 100, borrows := 50, collateralFactor := 1 }
  let solventBool : Bool := decide (lend.borrows ≤ lend.deposits * lend.collateralFactor)
  IO.println s!"lending_demo: deposits={lend.deposits}, borrows={lend.borrows}, collateralFactor={lend.collateralFactor}, solvent={solventBool}"
  pure 0

end DeFiDemo
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.DeFiDemo.main args
