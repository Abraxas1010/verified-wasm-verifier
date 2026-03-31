import HeytingLean.LeanCP.Core.HProp
import HeytingLean.LeanCP.Lang.CSyntax
import HeytingLean.LeanCP.VCG.WP
import HeytingLean.LeanCP.Tactics.Forward

/-!
# LeanCP Verified Smoke Examples

These are deliberately small fully-discharged VCG examples. They do not claim
algorithmic verification; they exist to prove that LeanCP has at least some
real `genVC` obligations discharged on the currently supported static fragment.

The two examples below specifically exercise the post-remediation WP behavior
for statically evaluable arithmetic and statically evaluable conditionals.

## Phase 6: Forward Tactic Tests

The second section exercises the forward tactic macros (`xstep`, `xentailer`)
from `Tactics/Forward.lean` against the state-sensitive `sgenVC` surface.
-/

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

def constArithBody : CStmt :=
  .ret (.binop .add (.intLit 2) (.intLit 3))

noncomputable def constArithSpec : CFunSpec where
  name := "const_arith"
  params := []
  retType := .int
  pre := HProp.emp
  post := fun retVal => HProp.pure (retVal = CVal.int 5)
  body := constArithBody

example : genVC constArithSpec := by
  intro h hempty
  subst hempty
  change (⌜CVal.int 5 = CVal.int 5⌝) Heap.empty
  simp [HProp.pure]

def staticBranchBody : CStmt :=
  .ite (.intLit 1) (.ret (.intLit 7)) (.ret (.intLit 9))

noncomputable def staticBranchSpec : CFunSpec where
  name := "static_branch"
  params := []
  retType := .int
  pre := HProp.emp
  post := fun retVal => HProp.pure (retVal = CVal.int 7)
  body := staticBranchBody

example : genVC staticBranchSpec := by
  intro h hempty
  subst hempty
  simp [staticBranchSpec, staticBranchBody, wp, HProp.pure, evalStaticExpr, isTruthy]

/-! ## Phase 6: Forward Tactic Smoke Tests

The tests below exercise `xstep` and `xentailer` on goals where the statement
constructor is visible — which is the normal situation after the user unfolds
spec/body definitions via `intro`/`simp only`. -/

section ForwardTacticTests

/-- `xstep` unfolds `swp` for a simple return and `xentailer` closes. -/
example : ∀ (st : CState),
    swp (.ret (.intLit 42)) (fun ret _ => ret = .int 42) st := by
  intro st
  xstep
  xentailer

/-- `xstep` unfolds through `swp` for a `seq` of assignment + return. -/
example : ∀ (st : CState),
    swp (.seq (.assign (.var "x") (.intLit 7)) (.ret (.var "x")))
      (fun ret _ => ret = .int 7) st := by
  intro st
  xstep
  xentailer

/-- `xstep` handles conditionals with statically evaluable guard. -/
example : ∀ (st : CState),
    swp (.ite (.intLit 1) (.ret (.intLit 10)) (.ret (.intLit 20)))
      (fun ret _ => ret = .int 10) st := by
  intro st
  xstep
  xentailer
  simp

/-- `xstep` unfolds `sgenVC` wrapper when the body is inlined. -/
example : sgenVC {
    name := "inline_ret"
    params := []
    retType := .int
    pre := fun _ => True
    post := fun ret _ => ret = .int 5
    body := .ret (.intLit 5)
  } := by
  xstep
  xentailer

/-- `xstep` on the call-aware `swpFull` surface. -/
example : ∀ (st : CState),
    swpFull (fun _ => none)
      (.ret (.intLit 99))
      (fun ret _ => ret = .int 99) st := by
  intro st
  xstep
  xentailer

end ForwardTacticTests

end HeytingLean.LeanCP.Examples
