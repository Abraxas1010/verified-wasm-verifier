import Mathlib.Tactic
import HeytingLean.MiniC.SDE
import HeytingLean.MiniC.Semantics
import HeytingLean.MiniC.ToWasmMiniFunCorrectness

/-!
# MiniC SDE codegen sanity checks (Phase 3)

These are small executable-style checks (as definitional equalities) that:
- generate a MiniC program from a tiny SDE,
- run selected generated functions via the MiniC big-step semantics,
- and compare against hand-computed integer results.
-/

namespace HeytingLean
namespace Tests
namespace MiniC
namespace SDE

open HeytingLean.MiniC
open HeytingLean.MiniC.SDE

/-! ## A tiny 2D, 1-noise demo SDE -/

private abbrev ι := Fin 2
private abbrev κ := Fin 1

private def demoSystem : CompilableSDESystem ι κ :=
  { drift := fun N i =>
      match i.1 with
      | 0 => Expr.add (Expr.var (N.x ⟨0, by decide⟩)) (Expr.var (N.x ⟨1, by decide⟩))
      | _ => Expr.sub (Expr.var (N.x ⟨0, by decide⟩)) (Expr.var (N.x ⟨1, by decide⟩))
    diffusion := fun _N _i _k => Expr.intLit 1 }

private def progSteps2 : Program :=
  translateSDESystem (ι := ι) (κ := κ) demoSystem (steps := 2)

private def findDef (p : Program) (nm : String) : Option Fun :=
  p.defs.find? (fun f => decide (f.name = nm))

/-! ## Step functions -/

example :
    (do
      let fn ← findDef progSteps2 "sde_euler_step_0"
      runFun fn [Val.int 2, Val.int 1, Val.int 1, Val.int 0])
      = some (Val.int 5) := by
  native_decide

example :
    (do
      let fn ← findDef progSteps2 "sde_euler_step_1"
      runFun fn [Val.int 2, Val.int 1, Val.int 1, Val.int 0])
      = some (Val.int 1) := by
  native_decide

example :
    (do
      let fn ← findDef progSteps2 "sde_stratonovich_step_0"
      runFun fn [Val.int 2, Val.int 1, Val.int 1, Val.int 0])
      = some (Val.int 9) := by
  native_decide

example :
    (do
      let fn ← findDef progSteps2 "sde_stratonovich_step_1"
      runFun fn [Val.int 2, Val.int 1, Val.int 1, Val.int 0])
      = some (Val.int 5) := by
  native_decide

/-! ## Unrolled trajectory simulator (Euler; steps=2, zero noise) -/

example :
    (do
      let fn ← findDef progSteps2 "sde_simulate_euler_0"
      -- params: dt, x0, x1, dW_0_0, dW_1_0
      runFun fn [Val.int 2, Val.int 1, Val.int 1, Val.int 0, Val.int 0])
      = some (Val.int 17) := by
  native_decide

example :
    (do
      let fn ← findDef progSteps2 "sde_simulate_euler_1"
      runFun fn [Val.int 2, Val.int 1, Val.int 1, Val.int 0, Val.int 0])
      = some (Val.int 9) := by
  native_decide

end SDE
end MiniC
end Tests
end HeytingLean
