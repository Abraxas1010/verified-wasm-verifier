import Lean
import HeytingLean.Economics.Game

/-
# economics_demo CLI

Tiny CLI that constructs a trivial two-player game instance and reports
that it has a (trivial) Nash equilibrium. This is a baseline that can
later be extended to simulate concrete staking or auction games.
-/

namespace HeytingLean
namespace CLI
namespace EconomicsDemo

open HeytingLean.Economics
open HeytingLean.Economics.Game
open HeytingLean.Governance

def main (argv : List String) : IO UInt32 := do
  let _ := argv
  IO.println "economics_demo: economics/game-theoretic core is available."
  IO.println "  Core example games:"
  IO.println "    • trivialGame"
  IO.println "    • stakingGame"
  IO.println "    • auctionTruthGame (fixed valuations)"
  IO.println "    • secondPriceGame (generic valuations)"
  -- Instantiate a simple valuation profile for the generic second-price game.
  let val : AuctionTruthPlayer → Nat := fun i => if i then 3 else 5
  IO.println ""
  IO.println s!"Example valuations: val false = {val false}, val true = {val true}"
  IO.println "  secondPriceGame val has truthful bidding as a Nash equilibrium."
  -- Sanity-check the bridge property for this instance.
  have hTruth :
      Bridge.propertyHolds (secondPriceGame val)
        Governance.Spec.PropertyId.auctionTruthfulness := by
    simpa [Bridge.propertyHolds] using
      secondPrice_incentiveCompatible (val := val)
  let _ := hTruth
  IO.println "  Bridge.propertyHolds _ .auctionTruthfulness is provable for this instance."
  IO.println "  (See HeytingLean.Economics.Game for full statements and proofs.)"
  pure 0

end EconomicsDemo
end CLI
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.EconomicsDemo.main args
