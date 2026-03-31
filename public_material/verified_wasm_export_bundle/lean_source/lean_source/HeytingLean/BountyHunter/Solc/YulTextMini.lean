import HeytingLean.BountyHunter.Solc.YulTextMini.Types
import HeytingLean.BountyHunter.Solc.YulTextMini.Parse
import HeytingLean.BountyHunter.Solc.YulTextMini.Effects
import HeytingLean.BountyHunter.Solc.YulTextMini.EffectSemantics
import HeytingLean.BountyHunter.Solc.YulTextMini.ToAlgebraIR
import HeytingLean.BountyHunter.Solc.YulTextMini.Json
import HeytingLean.BountyHunter.Solc.YulTextMini.Risk
import HeytingLean.BountyHunter.Solc.YulTextMini.AlphaRename
import HeytingLean.BountyHunter.Solc.YulTextMini.DeltaInvariants
import HeytingLean.BountyHunter.Solc.YulTextMini.CallInterface
import HeytingLean.BountyHunter.Solc.YulTextMini.Summary
import HeytingLean.BountyHunter.Solc.YulTextMini.Reachability
import HeytingLean.BountyHunter.Solc.YulTextMini.TemporalQuery
import HeytingLean.BountyHunter.Solc.YulTextMini.InvariantMining

/-!
# HeytingLean.BountyHunter.Solc.YulTextMini

Minimal Yul-text ingestion pipeline (solc `ir`/`irOptimized` strings):

- lex/parse a tiny Yul subset,
- extract a named function body,
- translate to AlgebraIR for checks.
-/
