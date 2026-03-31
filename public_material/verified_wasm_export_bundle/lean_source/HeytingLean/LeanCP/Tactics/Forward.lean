import HeytingLean.LeanCP.VCG.RecCallSound
import HeytingLean.LeanCP.Tactics.SimpLemmas
import HeytingLean.LeanCP.Tactics.XSimp

/-!
# LeanCP Forward Tactics

These are intentionally small macros over the verified symbolic surfaces. They
do not attempt VST-scale automation; they provide a stable first layer for the
common interactive steps:

- `xstep` unfolds one symbolic-execution layer from `swp`, `swpFull`,
  `swhileWP`, or `swhileWPFull`
- `xapp` applies the call-spec introduction rule
- `forward_call` instantiates `swpCall_intro` and cleans the resulting side goals
- `xentailer` simplifies the remaining state/separation obligations
- `forward_while inv` exposes the current bounded/unbounded loop surface
-/

namespace HeytingLean.LeanCP

open Lean Elab Tactic

syntax "xstep" : tactic
syntax "xapp" : tactic
syntax "forward_call" : tactic
syntax "xentailer" : tactic
syntax "xwhile " term : tactic
syntax "forward_while " term : tactic

macro_rules
  | `(tactic| xstep) => `(tactic|
      first
      -- simp only [swp, ...] is safe: these match on CStmt (not CExpr/CVal),
      -- so equation generation stays under the 200000 heartbeat limit (lean4#11546).
      | simp only [sgenVC, sgenVCFull, swp, swpFull, swpCall, swhileWP, swhileWPFull,
          evalArgs, callEntryState, restoreCallerState, bindCallEnv]
      | simp [sgenVC, sgenVCFull, swp, swpFull, swpCall, swhileWP, swhileWPFull,
          evalArgs, callEntryState, restoreCallerState, bindCallEnv])

macro_rules
  | `(tactic| xapp) => `(tactic|
      first
      | apply swpCall_intro
      | refine swpCall_intro ?_ ?_ ?_ ?_ ?_)

macro_rules
  | `(tactic| forward_call) => `(tactic|
      first
      | refine swpCall_intro ?_ ?_ ?_ ?_ ?_
      | apply swpCall_intro
      <;> try intros
      <;> try simp_all
      <;> try xentailer)

macro_rules
  | `(tactic| xentailer) => `(tactic|
      (try intros)
      -- Two-phase simplification to work around equation generation heartbeat
      -- bug (lean4#11546). evalBinOp/isTruthy equation generation exceeds the
      -- hardcoded 200000 heartbeat limit after CVal.float was added.
      -- Phase 1: cheap reductions (evalExpr, evalStaticExpr, isTruthy are fast)
      <;> try simp only [evalExpr, evalStaticExpr, isTruthy,
          CState.lookupVar, CState.updateVar,
          SProp.ofHProp, SProp.hand, SProp.fact,
          evalArgs, callEntryState, restoreCallerState, bindCallEnv]
      <;> try rfl
      <;> try omega
      -- Phase 2: structural cleanup (if True, Option.bind, etc.)
      <;> try simp
      -- Phase 3: if still open, try expensive defs
      <;> try simp only [evalBinOp, isTruthy]
      <;> try rfl
      <;> try simp_all
      <;> try omega
      <;> try leancp_xsimp)

macro_rules
  | `(tactic| xwhile $iters) => `(tactic|
      refine ⟨?_, ?_⟩
      <;> first
        | exact $iters
        | skip)

macro_rules
  | `(tactic| forward_while $inv) => `(tactic|
      first
      | change swhileWP _ _ $inv _ _ _
      | refine while_partial_sound _ $inv _ ?_ ?_ ?_
      | refine while_hoare_sound _ $inv _ _ ?_ ?_ ?_ ?_)

end HeytingLean.LeanCP
