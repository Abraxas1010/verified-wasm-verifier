import HeytingLean.LeanCP.Core.Val
import HeytingLean.LeanCP.Core.Perm
import HeytingLean.LeanCP.Core.Mem
import HeytingLean.LeanCP.Core.MemHProp
import HeytingLean.LeanCP.Core.MemSepLog
import HeytingLean.LeanCP.Core.Heap
import HeytingLean.LeanCP.Core.HProp
import HeytingLean.LeanCP.Core.SepLog
import HeytingLean.LeanCP.Core.SProp
import HeytingLean.LeanCP.Core.StateSepLog
import HeytingLean.LeanCP.Core.VarLemmas
import HeytingLean.LeanCP.Core.SFrameRule
import HeytingLean.LeanCP.ProductionReadiness

import HeytingLean.LeanCP.Predicates.Store
import HeytingLean.LeanCP.Predicates.SLL
import HeytingLean.LeanCP.Predicates.DLL
import HeytingLean.LeanCP.Predicates.Tree
import HeytingLean.LeanCP.Predicates.Array

import HeytingLean.LeanCP.Lang.StructLayout
import HeytingLean.LeanCP.Lang.CSyntax
import HeytingLean.LeanCP.Lang.CSyntaxLemmas
import HeytingLean.LeanCP.Lang.CSemantics
import HeytingLean.LeanCP.Lang.CSemanticsDecEq
import HeytingLean.LeanCP.Lang.CParser

import HeytingLean.LeanCP.Annotations.Language
import HeytingLean.LeanCP.Annotations.Parser
import HeytingLean.LeanCP.Annotations.Elaborate
import HeytingLean.LeanCP.Annotations.Smoke

import HeytingLean.LeanCP.VCG.WP
import HeytingLean.LeanCP.VCG.SFunSpec
import HeytingLean.LeanCP.VCG.SWP
import HeytingLean.LeanCP.VCG.SWPSound
import HeytingLean.LeanCP.VCG.SWhile
import HeytingLean.LeanCP.VCG.WhileSound
import HeytingLean.LeanCP.VCG.SWPCallSound
import HeytingLean.LeanCP.VCG.RecCallSound
import HeytingLean.LeanCP.VCG.SymExec
import HeytingLean.LeanCP.VCG.SymExecSmoke
import HeytingLean.LeanCP.VCG.EndToEndSoundness
import HeytingLean.LeanCP.VCG.EndToEndSoundnessSmoke
import HeytingLean.LeanCP.VCG.SMT
import HeytingLean.LeanCP.VCG.SMTSmoke
import HeytingLean.LeanCP.VCG.Entailment
import HeytingLean.LeanCP.VCG.FrameRule

import HeytingLean.LeanCP.Tactics.XSimp
import HeytingLean.LeanCP.Tactics.Attrs
import HeytingLean.LeanCP.Tactics.SimpLemmas
import HeytingLean.LeanCP.Tactics.Forward
import HeytingLean.LeanCP.Tactics.LeanCPSolve
import HeytingLean.LeanCP.Tactics.Refute

import HeytingLean.LeanCP.Examples.ListReverse
import HeytingLean.LeanCP.Examples.ArraySum
import HeytingLean.LeanCP.Examples.TreeInsert
import HeytingLean.LeanCP.Examples.TwoSum
import HeytingLean.LeanCP.Examples.ListMerge
import HeytingLean.LeanCP.Examples.BinarySearch
import HeytingLean.LeanCP.Examples.DetectCycle
import HeytingLean.LeanCP.Examples.Strlen
import HeytingLean.LeanCP.Examples.Swap
import HeytingLean.LeanCP.Examples.SwapVerified
import HeytingLean.LeanCP.Examples.TwoSumVerified
import HeytingLean.LeanCP.Examples.ArraySumVerified
import HeytingLean.LeanCP.Examples.IncrementVerified
import HeytingLean.LeanCP.Examples.MaxVerified
import HeytingLean.LeanCP.Examples.CountdownVerified
import HeytingLean.LeanCP.Examples.BlockScopeVerified
import HeytingLean.LeanCP.Examples.ListReverseVerified
import HeytingLean.LeanCP.Examples.CallerVerified
import HeytingLean.LeanCP.Examples.FactorialVerified
import HeytingLean.LeanCP.Examples.MutualRecursionVerified
import HeytingLean.LeanCP.Examples.BinarySearchVerified
import HeytingLean.LeanCP.Examples.FreeListVerified
import HeytingLean.LeanCP.Examples.HashTableVerified
import HeytingLean.LeanCP.Examples.InsertionSortVerified
import HeytingLean.LeanCP.Examples.StackVerified
import HeytingLean.LeanCP.Examples.StrlenVerified
import HeytingLean.LeanCP.Examples.TreeInsertVerified
import HeytingLean.LeanCP.Examples.ListMergeVerified
import HeytingLean.LeanCP.Examples.SwapVerifiedTactic
import HeytingLean.LeanCP.Examples.CallerVerifiedTactic
import HeytingLean.LeanCP.Examples.ListReverseVerifiedTactic
import HeytingLean.LeanCP.Examples.FreeList
import HeytingLean.LeanCP.Examples.VerifiedSmoke
import HeytingLean.LeanCP.Bench.Meta
import HeytingLean.LeanCP.Bench.ScalarArithmetic
import HeytingLean.LeanCP.Bench.Seed
import HeytingLean.LeanCP.Bench.Registry
import HeytingLean.LeanCP.Bench.Audit
import HeytingLean.LeanCP.Modular.VSU
import HeytingLean.LeanCP.Modular.Compose
import HeytingLean.LeanCP.Modular.Linking
import HeytingLean.LeanCP.Modular.Smoke
import HeytingLean.LeanCP.RealWorld.RealWorld

/-!
# LeanCP: Lean-Native C Program Verifier with Separation Logic

The first Lean 4-native tool for verifying C programs annotated with
separation logic specifications. Generates Lean proof obligations
dischargeable by SMT solvers (Z3, CVC5) or interactively.

## Architecture
- **Core/** — Heap model, heap propositions, separation logic, and state-sensitive assertions
- **Predicates/** — Standard predicates (sll, tree, array, store)
- **Lang/** — Deep-embedded C AST, operational semantics, parser, and struct layouts
- **VCG/** — Heap-only WP, a state-sensitive SWP with loop-free tail-return soundness, a bounded while rule, an unbounded partial-correctness while soundness layer, and recursive/mutual call soundness
- **Tactics/** — leancp_solve (SMT dispatch), xsimp, a tagged simp/unfold DB, forward/xapp/xentailer macros, refutation
- **Examples/** — AST encodings, static-fragment smoke tests, discharged state-sensitive swap/two-sum/increment/max/countdown/caller proofs, canonical benchmark proofs (`ArraySumVerified`, `ListReverseVerified`), tactic-assisted re-proofs, recursive consumers (`FactorialVerified`, `MutualRecursionVerified`), and production-pattern examples for nested loops, arrays, malloc/free, structs, and call integration (`InsertionSortVerified`, `BinarySearchVerified`, `FreeListVerified`, `HashTableVerified`, `StackVerified`)
- **Bench/** — Typed benchmark metadata, seeded theorem/program registry, and computed suite-audit gates for the Phase 8 benchmark portfolio
- **Modular/** — VSU-style verified procedure packaging, binary composition/linking, and modular smoke evidence over imported/exported call contracts
- **RealWorld/** — a libc-lite real-world slice with verified `strlen`, `strnlen`, `memset`, `memcpy`, and `bzero` APIs over concrete byte/string predicates

## Production Status
LeanCP now exposes the full Phase 1-8 production-tool surface requested by the
March 18, 2026 PM: shared lemma hardening, state frame rule, unbounded while
partial correctness, recursive/mutual call soundness, expanded C constructors,
forward-tactic helpers, a typed annotation frontend, and an audited benchmark
portfolio over the verified LeanCP example surface. Phase 9 adds a first
modular verification layer: independently verified exports can now be packaged
into VSUs, composed under export-name disjointness, and linked with fail-closed
import resolution. Phase 10 adds a first real-world `libc-lite` slice on top of
the same core proof substrate.

## Positioning
| System | Strength | Current LeanCP relation |
|--------|----------|--------------------------|
| QCP | Larger verified-function portfolio and broader benchmark count | LeanCP is still smaller in volume, but now has a comparable portfolio shape: loops, recursion, calls, arrays, structs, and heap lifecycle examples |
| VST | Deep mature automation and CompCert-backed semantic stack | LeanCP matches the canonical proof pattern on benchmark examples, but not VST's scale or backend maturity |
| CN / Cerberus | Rich C-language semantic analysis and standards-facing modeling | LeanCP remains a verifier-first deep embedding rather than a full standards model, but now exposes a broader executable/verified C surface |
-/
