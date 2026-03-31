import HeytingLean.BountyHunter.AlgebraIR
import HeytingLean.BountyHunter.AlgebraIR2
import HeytingLean.BountyHunter.YulMini
import HeytingLean.BountyHunter.Solc.ExtractIR
import HeytingLean.BountyHunter.Foundry.OracleChain

/-!
# HeytingLean.BountyHunter

Executable-first bug bounty hunter for smart contract security (Phase 0).

## Overview

This namespace currently focuses on the **AlgebraIR choke point**:

- represent security-relevant behavior in a small, canonical IR,
- run executable checks that produce deterministic JSON,
- emit constructive witnesses on failure.

Higher-level proof-carrying artifacts and concrete replay are staged follow-ons.

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    BountyHunter (Phase 0)                       │
├─────────────────────────────────────────────────────────────────┤
│  YulMini JSON  ──▶  AlgebraIR CFG  ──▶  Check(s)  ──▶  Verdict  │
│      │                 │                (e.g. CEI)      +      │
│      │                 │                                  JSON │
│      └── solc JSON ──▶ Extract IR string (no parsing yet)      │
└─────────────────────────────────────────────────────────────────┘
```

## Modules

### AlgebraIR (`AlgebraIR/`)
Deterministic JSON I/O + CFG checks (Phase 0).

### YulMini (`YulMini/`)
A minimal Yul-adjacent input language with deterministic JSON + translation to AlgebraIR.

### Solc (`Solc/`)
Extract `ir`/`irOptimized` strings from solc standard-json output (no parsing yet).

## References

- "Finding The Greedy, Prodigal, and Suicidal Contracts at Scale" (ACSAC 2018)
- "Securify: Practical Security Analysis of Smart Contracts" (CCS 2018)
- EtherStore reentrancy pattern (Solidity by Example)
-/
