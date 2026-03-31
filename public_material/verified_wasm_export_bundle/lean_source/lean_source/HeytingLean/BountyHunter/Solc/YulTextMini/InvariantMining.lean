import Std
import Lean.Data.Json
import HeytingLean.BountyHunter.Solc.YulTextMini.Reachability
import HeytingLean.BountyHunter.Solc.YulTextMini.Risk

/-!
# HeytingLean.BountyHunter.Solc.YulTextMini.InvariantMining

Phase 8: **expanded invariant mining** (MVP).

This module defines a stable `MinedInvariant` JSON schema used by the solc CLI mode
`--solc-mine-invariants`. Invariants can be mined from:
- closure/reachability properties (WP5-lite),
- risk scan primitives (origin/timestamp/delegatecall/etc),
- call-interface risk flags, delta inconsistencies, etc. (wired in the CLI).
-/

namespace HeytingLean.BountyHunter.Solc.YulTextMini

open Lean

structure MinedInvariant where
  version : String := "bh.yultextmini.mined_invariant.v0"
  id : String
  kind : String
  violated : Bool
  reason : String
  evidence : Json := Json.null
  deriving Inhabited

def MinedInvariant.toJson (i : MinedInvariant) : Json :=
  Json.mkObj
    [ ("version", Json.str i.version)
    , ("id", Json.str i.id)
    , ("kind", Json.str i.kind)
    , ("violated", Json.bool i.violated)
    , ("reason", Json.str i.reason)
    , ("evidence", i.evidence)
    ]

def MinedInvariant.ofClosure (c : ClosureInvariant) : MinedInvariant :=
  { id := c.id
    kind := "closure"
    violated := c.violated
    reason := c.reason
    evidence := c.toJson
  }

def minedOfRisk (r : RiskReport) : Array MinedInvariant :=
  #[
    { id := "no_tx_origin_auth"
      kind := "risk"
      violated := r.usesOrigin
      reason := "risk scan: tx.origin observed"
      evidence := riskToJson r
    },
    { id := "no_timestamp_randomness"
      kind := "risk"
      violated := r.usesTimestamp
      reason := "risk scan: block.timestamp observed"
      evidence := riskToJson r
    },
    { id := "no_blockhash_randomness"
      kind := "risk"
      violated := r.usesBlockhash
      reason := "risk scan: blockhash observed"
      evidence := riskToJson r
    },
    { id := "no_prevrandao_randomness"
      kind := "risk"
      violated := r.usesPrevrandao
      reason := "risk scan: prevrandao observed"
      evidence := riskToJson r
    },
    { id := "no_selfdestruct"
      kind := "risk"
      violated := r.usesSelfdestruct
      reason := "risk scan: selfdestruct observed"
      evidence := riskToJson r
    },
    { id := "no_delegatecall"
      kind := "risk"
      violated := r.usesDelegatecall || r.usesCallcode
      reason := "risk scan: delegatecall/callcode observed"
      evidence := riskToJson r
    },
    { id := "check_low_level_call_return"
      kind := "risk"
      violated := r.uncheckedCallReturn
      reason := "risk scan: unchecked low-level call return observed"
      evidence := riskToJson r
    }
  ]

end HeytingLean.BountyHunter.Solc.YulTextMini

