import HeytingLean.LeanCP.VCG.SWPSound
import HeytingLean.LeanCP.Core.VarLemmas

/-!
# LeanCP Example: Verified Increment

State-sensitive verification of a single pointer update.
-/

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

set_option linter.unnecessarySimpa false
set_option maxHeartbeats 800000

def incrBody : CStmt :=
  .assign (.deref (.var "p")) (.binop .add (.deref (.var "p")) (.intLit 1))

def incrSSpec (addr : Nat) (n : Int) : SFunSpec where
  name := "increment_state_sensitive"
  params := [("p", .ptr .int)]
  retType := .void
  pre := fun st =>
    st.lookupVar "p" = some (.ptr 0 (Int.ofNat addr)) ∧
    st.heap.read addr = some (.int n)
  post := fun _ st =>
    st.heap.read addr = some (.int (n + 1))
  body := incrBody

private theorem incr_loopFree : LoopFree incrBody := by
  simp [incrBody, LoopFree]

private theorem incr_tailReturn : TailReturn incrBody := by
  simp [incrBody, TailReturn]

set_option maxHeartbeats 800000 in
theorem incr_verified (addr : Nat) (n : Int) :
    sgenVC (incrSSpec addr n) := by
  intro st hpre
  rcases hpre with ⟨hp, hread⟩
  have hEvalP : evalExpr (.var "p") st = some (.ptr 0 (Int.ofNat addr)) := by
    simpa [evalExpr] using hp
  have hReadPtr : st.readPtr addr = some (.int n) := by
    simpa [hread] using (CState.readPtr_block0 st addr addr)
  have hEvalDeref : evalExpr (.deref (.var "p")) st = some (.int n) := by
    simpa [evalExpr, evalStaticExpr, hEvalP] using hReadPtr
  have hStaticRhs :
      evalStaticExpr (.binop .add (.deref (.var "p")) (.intLit 1)) = none := by
    simp [evalStaticExpr]
  have hEvalOne : evalExpr (.intLit 1) st = some (.int 1) := by
    rfl
  have hEvalRhs :
      evalExpr (.binop .add (.deref (.var "p")) (.intLit 1)) st = some (.int (n + 1)) := by
    rw [evalExpr, hStaticRhs, hEvalDeref, hEvalOne]
    · rfl
    · intro h
      cases h
    · intro h
      cases h
  let st' : CState := st.withHeap (st.heap.write addr (.int (n + 1)))
  have hWritePtr : st.writePtr addr (.int (n + 1)) = some st' := by
    simpa [st'] using (CState.writePtr_block0 st addr addr (.int (n + 1)))
  have hpost : (incrSSpec addr n).post CVal.undef st' := by
    simpa [incrSSpec, st'] using heap_read_write_eq st.heap addr (.int (n + 1))
  have hpair :
      (∃ vOld, st.readPtr addr = some vOld) ∧
        ∃ st'', st.writePtr addr (.int (n + 1)) = some st'' ∧ (incrSSpec addr n).post CVal.undef st'' := by
    exact ⟨⟨.int n, hReadPtr⟩, ⟨st', hWritePtr, hpost⟩⟩
  change swp incrBody (incrSSpec addr n).post st
  simpa [incrBody, swp, hEvalP, hEvalRhs, st'] using hpair

theorem incr_executes (addr : Nat) (n : Int) {st fuel}
    (hpre : (incrSSpec addr n).pre st)
    (hfuel : stmtDepth incrBody ≤ fuel) :
    ∃ res, execStmt fuel incrBody st = some res ∧
      match res with
      | .returned v st' => (incrSSpec addr n).post v st'
      | .normal st' => (incrSSpec addr n).post CVal.undef st' := by
  have hvc : swp incrBody (incrSSpec addr n).post st :=
    incr_verified addr n st hpre
  exact swp_sound incrBody incr_loopFree incr_tailReturn hfuel hvc

end HeytingLean.LeanCP.Examples
