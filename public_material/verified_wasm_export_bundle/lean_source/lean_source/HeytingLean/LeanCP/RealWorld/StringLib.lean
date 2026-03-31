import HeytingLean.LeanCP.RealWorld.MemsetVerified
import HeytingLean.LeanCP.Examples.StrlenVerified
import HeytingLean.LeanCP.Core.VarLemmas

namespace HeytingLean.LeanCP.RealWorld

open HeytingLean.LeanCP

set_option linter.unnecessarySimpa false

/-- Real-world export of the existing `strlen` proof on the shared support
predicate. -/
theorem strlen_correct (chars : List Int) (base : Nat) :
    ∀ st,
      st.lookupVar "s" = some (CVal.ptrAddr (base : PtrVal)) →
      stringAt_s base chars st →
      (∀ (i : Nat) (c : Int), chars[i]? = some c → c ≠ 0) →
      ∃ st',
        execStmt (swhileFuel HeytingLean.LeanCP.Examples.strlenLoopBody chars.length + 2)
          HeytingLean.LeanCP.Examples.strlenBody st =
            some (.returned (.int (Int.ofNat chars.length)) st') ∧
        stringAt_s base chars st' := by
  intro st hs hstring hnz
  simpa [stringAt_s] using
    (HeytingLean.LeanCP.Examples.strlen_correct chars base st hs hstring hnz)

def bzeroBody : CStmt :=
  .seq (.assign (.var "value") (.intLit 0)) memsetBody

theorem bzero_correct (base n : Nat) :
    ∀ st,
      st.lookupVar "dst" = some (CVal.ptrAddr (base : PtrVal)) →
      st.lookupVar "n" = some (.int (Int.ofNat n)) →
      allocated_s base n st →
      ∃ st',
        execStmt (swhileFuel memsetLoopBody n + 3) bzeroBody st =
          some (.returned (CVal.ptrAddr (base : PtrVal)) st') ∧
        filled_s base n 0 st' := by
  intro st hdst hn halloc
  let st1 := st.updateVar "value" (.int 0)
  have hdst1 : st1.lookupVar "dst" = some (CVal.ptrAddr (base : PtrVal)) := by
    calc
      st1.lookupVar "dst" = st.lookupVar "dst" := by
        simpa [st1] using lookupVar_updateVar_ne st "value" "dst" (.int 0)
          (by decide : "dst" ≠ "value")
      _ = some (CVal.ptrAddr (base : PtrVal)) := hdst
  have hval1 : st1.lookupVar "value" = some (.int 0) := by
    simpa [st1] using lookupVar_updateVar_eq st "value" (.int 0)
  have hn1 : st1.lookupVar "n" = some (.int (Int.ofNat n)) := by
    calc
      st1.lookupVar "n" = st.lookupVar "n" := by
        simpa [st1] using lookupVar_updateVar_ne st "value" "n" (.int 0)
          (by decide : "n" ≠ "value")
      _ = some (.int (Int.ofNat n)) := hn
  have halloc1 : allocated_s base n st1 := by
    simpa [st1] using (allocated_s_updateVar base n st "value" (.int 0)).2 halloc
  rcases memset_correct base n 0 st1 hdst1 hval1 hn1 halloc1 with ⟨st', hExec, hFilled⟩
  refine ⟨st', ?_, hFilled⟩
  change execStmt (Nat.succ (swhileFuel memsetLoopBody n + 2)) bzeroBody st =
    some (.returned (CVal.ptrAddr (base : PtrVal)) st')
  simpa [bzeroBody, execStmt, st1] using hExec

end HeytingLean.LeanCP.RealWorld
