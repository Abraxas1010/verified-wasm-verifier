import Std
import HeytingLean.BountyHunter.Solc.YulTextMini.Types
import HeytingLean.BountyHunter.Solc.YulTextMini.Effects
import HeytingLean.BountyHunter.AlgebraIR.Types

/-!
# HeytingLean.BountyHunter.Solc.YulTextMini.EffectSemantics

Minimal “semantic spine” for Phase 0 security checks over Yul-text:

- We intentionally do **not** model value-level semantics (u256, memory, ABI, etc.).
- We *do* model (deterministically) the **abstract effect trace** we care about
  for checks like dominance/CEI: `sload/sstore/(delegate)call/...`.

This module provides a single, explicit definition of that effect semantics so
other parts of the system can cite it, and so we can attach correctness claims
to it (even if the global EVM/solc correctness story is a larger follow-on).
-/

namespace HeytingLean.BountyHunter.Solc.YulTextMini

open HeytingLean.BountyHunter.AlgebraIR

/-! The “local state” we track for effect semantics is a symbolic environment:
`let`/`assign` bindings map variable names to AST expressions (not values).

This is used only to expand storage slot expressions so our trace is more
informative and more stable across minor `solc` transformations.
-/
structure EffState where
  env : Env := envEmpty
  deriving Inhabited

/-- Evaluate a single statement in the effect semantics. -/
def evalStmt (st : EffState) (s : Stmt) : EffState × Array Effect :=
  let effs := expectedEffectsFromStmt st.env s
  let env' := updateEnv st.env s
  ({ env := env' }, effs)

/-- Final environment after processing statements left-to-right. -/
def finalEnv (env0 : Env) (ss : Array Stmt) : Env :=
  ss.foldl (fun env s => updateEnv env s) env0

/-- Evaluate a statement list in the effect semantics. -/
def evalStmts (st0 : EffState) (ss : Array Stmt) : EffState × Array Effect :=
  ({ env := finalEnv st0.env ss }, expectedEffectsFromStmts st0.env ss)

@[simp] theorem evalStmt_effects (st : EffState) (s : Stmt) :
    (evalStmt st s).2 = expectedEffectsFromStmt st.env s := by
  rfl

@[simp] theorem evalStmt_env (st : EffState) (s : Stmt) :
    (evalStmt st s).1.env = updateEnv st.env s := by
  rfl

theorem evalStmts_effects (st : EffState) (ss : Array Stmt) :
    (evalStmts st ss).2 = expectedEffectsFromStmts st.env ss := by
  rfl

theorem evalStmts_env (st : EffState) (ss : Array Stmt) :
    (evalStmts st ss).1.env = finalEnv st.env ss := by
  rfl

end HeytingLean.BountyHunter.Solc.YulTextMini
