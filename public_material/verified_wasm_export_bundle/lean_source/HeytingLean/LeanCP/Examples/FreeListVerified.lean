import HeytingLean.LeanCP.Examples.FreeList
import HeytingLean.LeanCP.Lang.CSemanticsDecEq
import HeytingLean.LeanCP.Core.VarLemmas
import HeytingLean.LeanCP.Tactics.Forward

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

def freedAt (addrs : Finset Nat) (st : CState) : Prop :=
  ∀ addr, addr ∈ addrs → st.heap.read addr = none

def freeListWhileFuel : List Int → Nat
  | [] => 1
  | _ :: xs => max 4 (freeListWhileFuel xs) + 1

def freeListBodyFuel (xs : List Int) : Nat :=
  freeListWhileFuel xs + 1

def freeListCond : CExpr :=
  .binop .ne (.var "curr") .null

def freeListLoopBody : CStmt :=
  .seq (.assign (.var "next") (.fieldAccess (.var "curr") "next"))
    (.seq (.free (.var "curr") 2)
      (.assign (.var "curr") (.var "next")))

private theorem resolvePtr_updateVar (st : CState) (x : String) (v : CVal) (ptr : PtrVal) :
    (st.updateVar x v).resolvePtr ptr = st.resolvePtr ptr := by
  cases st
  rfl

private theorem freedAt_updateVar
    (addrs : Finset Nat) (st : CState) (x : String) (v : CVal)
    (hfreed : freedAt addrs st) :
    freedAt addrs (st.updateVar x v) := by
  intro addr hmem
  simpa [freedAt] using hfreed addr hmem

private theorem heap_read_free_ne
    (h : Heap) (freeAddr readAddr : Nat) (hneq : readAddr ≠ freeAddr) :
    (h.free freeAddr).read readAddr = h.read readAddr := by
  simp [Heap.read, Heap.free, Finmap.lookup_erase, hneq]

private theorem freeBlock_two (heap : Heap) (base : Nat) :
    freeBlock heap base 2 = (heap.free base).free (base + 1) := by
  have hrange : List.range 2 = [0, 1] := by decide
  simp [freeBlock, hrange]

private theorem freeCells_read_eq_none
    (st : CState) (base : Nat) :
    (st.freeCells base 2).heap.read base = none := by
  simp [CState.freeCells, freeBlock_two, Heap.read, Heap.free]

private theorem freeCells_read_next_eq_none
    (st : CState) (base : Nat) :
    (st.freeCells base 2).heap.read (base + 1) = none := by
  have hne : base + 1 ≠ base := Nat.succ_ne_self base
  simp [CState.freeCells, freeBlock_two, Heap.read, Heap.free, Finmap.lookup_erase,
    hne]

private theorem freeCells_read_preserve
    (st : CState) (base addr : Nat)
    (hneq0 : addr ≠ base) (hneq1 : addr ≠ base + 1) :
    (st.freeCells base 2).heap.read addr = st.heap.read addr := by
  calc
    (st.freeCells base 2).heap.read addr
        = ((st.heap.free base).free (base + 1)).read addr := by
            simp [CState.freeCells, freeBlock_two]
    _ = (st.heap.free base).read addr := by
          simpa using heap_read_free_ne (st.heap.free base) (base + 1) addr hneq1
    _ = st.heap.read addr := by
          simpa using heap_read_free_ne st.heap base addr hneq0

private theorem freedAt_freeCells_preserves
    (addrs : Finset Nat) (st : CState) (base : Nat)
    (hfreed : freedAt addrs st)
    (hnot0 : base ∉ addrs)
    (hnot1 : base + 1 ∉ addrs) :
    freedAt addrs (st.freeCells base 2) := by
  intro addr hmem
  have hneq0 : addr ≠ base := by
    intro hEq
    apply hnot0
    simpa [hEq] using hmem
  have hneq1 : addr ≠ base + 1 := by
    intro hEq
    apply hnot1
    simpa [hEq] using hmem
  rw [freeCells_read_preserve st base addr hneq0 hneq1]
  exact hfreed addr hmem

private theorem sll_s_addrs_freeCells_eq
    (ptr : CVal) (xs : List Int) (st : CState) {addr : Nat}
    (hnotData : addr ∉ sll_s_addrs ptr xs st)
    (hnotNext : addr + 1 ∉ sll_s_addrs ptr xs st) :
    sll_s_addrs ptr xs (st.freeCells addr 2) = sll_s_addrs ptr xs st := by
  let st1 : CState := { st with heap := st.heap.free addr }
  have haddrs1 : sll_s_addrs ptr xs st1 = sll_s_addrs ptr xs st := by
    simpa [st1] using sll_s_addrs_free_eq ptr xs st hnotData
  have hnotNext1 : addr + 1 ∉ sll_s_addrs ptr xs st1 := by
    simpa [haddrs1] using hnotNext
  have haddrs2 :
      sll_s_addrs ptr xs { st1 with heap := st1.heap.free (addr + 1) } =
        sll_s_addrs ptr xs st1 := by
    simpa [st1] using sll_s_addrs_free_eq ptr xs st1 hnotNext1
  have hheap :
      ({ st1 with heap := st1.heap.free (addr + 1) }).heap = (st.freeCells addr 2).heap := by
    simp [st1, CState.freeCells, freeBlock_two]
  have hEqState :
      sll_s_addrs ptr xs { st1 with heap := st1.heap.free (addr + 1) } =
        sll_s_addrs ptr xs (st.freeCells addr 2) := by
    simpa [hheap] using
      (sll_s_addrs_same_heap ptr xs ({ st1 with heap := st1.heap.free (addr + 1) }).heap
        { st1 with heap := st1.heap.free (addr + 1) }.env (st.freeCells addr 2).env
        { st1 with heap := st1.heap.free (addr + 1) }.nextAddr (st.freeCells addr 2).nextAddr
        { st1 with heap := st1.heap.free (addr + 1) }.mem (st.freeCells addr 2).mem
        { st1 with heap := st1.heap.free (addr + 1) }.allocs (st.freeCells addr 2).allocs)
  calc
    sll_s_addrs ptr xs (st.freeCells addr 2)
        = sll_s_addrs ptr xs { st1 with heap := st1.heap.free (addr + 1) } := hEqState.symm
    _ = sll_s_addrs ptr xs st1 := haddrs2
    _ = sll_s_addrs ptr xs st := haddrs1

private theorem freeListCond_eval_null
    (st : CState)
    (hcurr : st.lookupVar "curr" = some .null) :
    evalExpr freeListCond st = some (.int 0) := by
  simpa [freeListCond, evalExpr, evalStaticExpr, hcurr] using
    (show evalBinOp .ne .null .null = some (.int 0) by rfl)

private theorem freeListCond_eval_ptr
    (st : CState) (base : Nat)
    (hcurr : st.lookupVar "curr" = some (.ptr 0 (Int.ofNat base))) :
    evalExpr freeListCond st = some (.int 1) := by
  simpa [freeListCond, evalExpr, evalStaticExpr, hcurr] using
    (show evalBinOp .ne (.ptr 0 (Int.ofNat base)) .null = some (.int 1) by rfl)

def freeListInv (head : CVal) (fullAddrs : Finset Nat) : SProp := fun st =>
  ∃ curr rem,
    st.lookupVar "head" = some head ∧
    st.lookupVar "curr" = some curr ∧
    sll_s curr rem st ∧
    freedAt (fullAddrs \ sll_s_addrs curr rem st) st

def freeListLoopPost (head : CVal) (fullAddrs : Finset Nat) : CVal → SProp := fun _ st =>
  st.lookupVar "head" = some head ∧
  st.lookupVar "curr" = some .null ∧
  freedAt fullAddrs st

private theorem freeList_eval_next_field
    (st : CState) (base : Nat) (next : CVal)
    (hcurr : st.lookupVar "curr" = some (.ptr 0 (Int.ofNat base)))
    (hnext : st.heap.read (base + 1) = some next) :
    evalExpr (.fieldAccess (.var "curr") "next") st = some next := by
  have hnonneg : 0 ≤ (Int.ofNat base + 1 : Int) := by
    exact Int.add_nonneg (Int.natCast_nonneg _) (by decide)
  simpa [evalExpr, evalStaticExpr, hcurr, fieldOffset, PtrVal.addOffset, Addr.addOffset,
    CState.readPtr, CState.resolvePtr, hnonneg] using hnext

private theorem freeList_lookup_curr_after_set_next
    (st : CState) (next : CVal) :
    (st.updateVar "next" next).lookupVar "curr" = st.lookupVar "curr" := by
  simpa using lookupVar_updateVar_ne st "next" "curr" next (by simp : "curr" ≠ "next")

private theorem freeList_eval_curr_after_set_next
    (st : CState) (curr next : CVal)
    (hcurr : st.lookupVar "curr" = some curr) :
    evalExpr (.var "curr") (st.updateVar "next" next) = some curr := by
  simpa [evalExpr, evalStaticExpr, freeList_lookup_curr_after_set_next st next] using hcurr

private theorem freeList_resolve_curr_after_set_next
    (st : CState) (base : Nat) (next : CVal) :
    (st.updateVar "next" next).resolvePtr { block := 0, offset := Int.ofNat base } = some base := by
  simpa [resolvePtr_updateVar] using (CState.resolvePtr_block0 st base base)

private theorem freeList_lookup_next_after_free
    (st : CState) (base : Nat) (next : CVal) :
    (((st.updateVar "next" next).freeCells base 2)).lookupVar "next" = some next := by
  cases st
  rfl

private theorem freeList_eval_next_after_free
    (st : CState) (base : Nat) (next : CVal)
    (hnext : (((st.updateVar "next" next).freeCells base 2)).lookupVar "next" = some next) :
    evalExpr (.var "next") (((st.updateVar "next" next).freeCells base 2)) = some next := by
  simpa [evalExpr, evalStaticExpr] using hnext

private theorem freeList_assign_next_exec
    (st : CState) (base : Nat) (next : CVal)
    (hcurr : st.lookupVar "curr" = some (.ptr 0 (Int.ofNat base)))
    (hnext : st.heap.read (base + 1) = some next) :
    execStmt 3 (.assign (.var "next") (.fieldAccess (.var "curr") "next")) st =
      some (.normal (st.updateVar "next" next)) := by
  have hEval :
      evalExpr (.fieldAccess (.var "curr") "next") st = some next :=
    freeList_eval_next_field st base next hcurr hnext
  simp [execStmt, hEval]

private theorem freeList_assign_next_exec_fuel
    (fuel : Nat) (st : CState) (base : Nat) (next : CVal)
    (hcurr : st.lookupVar "curr" = some (.ptr 0 (Int.ofNat base)))
    (hnext : st.heap.read (base + 1) = some next) :
    execStmt (fuel + 3) (.assign (.var "next") (.fieldAccess (.var "curr") "next")) st =
      some (.normal (st.updateVar "next" next)) := by
  have hEval :
      evalExpr (.fieldAccess (.var "curr") "next") st = some next :=
    freeList_eval_next_field st base next hcurr hnext
  cases fuel <;> simp [execStmt, hEval]

private theorem freeList_free_curr_exec
    (st : CState) (base : Nat) (next : CVal)
    (hcurr : st.lookupVar "curr" = some (.ptr 0 (Int.ofNat base))) :
    execStmt 2 (.free (.var "curr") 2) (st.updateVar "next" next) =
      some (.normal ((st.updateVar "next" next).freeCells base 2)) := by
  have hEvalCurr :
      evalExpr (.var "curr") (st.updateVar "next" next) = some (.ptr 0 (Int.ofNat base)) := by
    simpa using
      freeList_eval_curr_after_set_next st (.ptr 0 (Int.ofNat base)) next hcurr
  have hResolve :
      (st.updateVar "next" next).resolvePtr { block := 0, offset := Int.ofNat base } = some base :=
    freeList_resolve_curr_after_set_next st base next
  simp [execStmt, hEvalCurr]
  change
    (((st.updateVar "next" next).resolvePtr { block := 0, offset := Int.ofNat base }).bind
        fun flatAddr => some (ExecResult.normal ((st.updateVar "next" next).freeCells flatAddr 2))) =
      some (ExecResult.normal ((st.updateVar "next" next).freeCells base 2))
  rw [hResolve]
  simp

private theorem freeList_free_curr_exec_fuel
    (fuel : Nat) (st : CState) (base : Nat) (next : CVal)
    (hcurr : st.lookupVar "curr" = some (.ptr 0 (Int.ofNat base))) :
    execStmt (fuel + 2) (.free (.var "curr") 2) (st.updateVar "next" next) =
      some (.normal ((st.updateVar "next" next).freeCells base 2)) := by
  have hEvalCurr :
      evalExpr (.var "curr") (st.updateVar "next" next) = some (.ptr 0 (Int.ofNat base)) := by
    simpa using
      freeList_eval_curr_after_set_next st (.ptr 0 (Int.ofNat base)) next hcurr
  have hResolve :
      (st.updateVar "next" next).resolvePtr { block := 0, offset := Int.ofNat base } = some base :=
    freeList_resolve_curr_after_set_next st base next
  cases fuel <;> simp [execStmt, hEvalCurr]
  all_goals
    change
      (((st.updateVar "next" next).resolvePtr { block := 0, offset := Int.ofNat base }).bind
          fun flatAddr => some (ExecResult.normal ((st.updateVar "next" next).freeCells flatAddr 2))) =
        some (ExecResult.normal ((st.updateVar "next" next).freeCells base 2))
    rw [hResolve]
    simp

private theorem freeList_assign_curr_exec
    (st : CState) (base : Nat) (next : CVal) :
    execStmt 2 (.assign (.var "curr") (.var "next")) (((st.updateVar "next" next).freeCells base 2)) =
      some (.normal ((((st.updateVar "next" next).freeCells base 2).updateVar "curr" next))) := by
  have hLookup :
      (((st.updateVar "next" next).freeCells base 2)).lookupVar "next" = some next :=
    freeList_lookup_next_after_free st base next
  have hEval :
      evalExpr (.var "next") (((st.updateVar "next" next).freeCells base 2)) = some next :=
    freeList_eval_next_after_free st base next hLookup
  simp [execStmt, hEval]

private theorem freeList_assign_curr_exec_fuel
    (fuel : Nat) (st : CState) (base : Nat) (next : CVal) :
    execStmt (fuel + 2) (.assign (.var "curr") (.var "next")) (((st.updateVar "next" next).freeCells base 2)) =
      some (.normal ((((st.updateVar "next" next).freeCells base 2).updateVar "curr" next))) := by
  have hLookup :
      (((st.updateVar "next" next).freeCells base 2)).lookupVar "next" = some next :=
    freeList_lookup_next_after_free st base next
  have hEval :
      evalExpr (.var "next") (((st.updateVar "next" next).freeCells base 2)) = some next :=
    freeList_eval_next_after_free st base next hLookup
  cases fuel <;> simp [execStmt, hEval]

private theorem freeListLoopBody_executes_from_state
    (st : CState) (base : Nat) (next : CVal)
    (hcurr : st.lookupVar "curr" = some (.ptr 0 (Int.ofNat base)))
    (hnext : st.heap.read (base + 1) = some next) :
    execStmt 4 freeListLoopBody st =
      some (.normal ((((st.updateVar "next" next).freeCells base 2).updateVar "curr" next))) := by
  have hAssignNext :
      execStmt 3 (.assign (.var "next") (.fieldAccess (.var "curr") "next")) st =
        some (.normal (st.updateVar "next" next)) :=
    freeList_assign_next_exec st base next hcurr hnext
  have hFree :
      execStmt 2 (.free (.var "curr") 2) (st.updateVar "next" next) =
        some (.normal ((st.updateVar "next" next).freeCells base 2)) :=
    freeList_free_curr_exec st base next hcurr
  have hAssignCurr :
      execStmt 2 (.assign (.var "curr") (.var "next")) (((st.updateVar "next" next).freeCells base 2)) =
        some (.normal ((((st.updateVar "next" next).freeCells base 2).updateVar "curr" next))) :=
    freeList_assign_curr_exec st base next
  have hTail :
      execStmt 3 (.seq (.free (.var "curr") 2) (.assign (.var "curr") (.var "next"))) (st.updateVar "next" next) =
        some (.normal ((((st.updateVar "next" next).freeCells base 2).updateVar "curr" next))) := by
    have hSeq :
        ((execStmt 2 (.free (.var "curr") 2) (st.updateVar "next" next)).bind
          fun r =>
            match r with
            | .normal st' => execStmt 2 (.assign (.var "curr") (.var "next")) st'
            | .returned v st' => some (.returned v st')) =
          some (.normal ((((st.updateVar "next" next).freeCells base 2).updateVar "curr" next))) := by
      rw [hFree]
      exact hAssignCurr
    simpa [execStmt] using hSeq
  have hSeq :
      ((execStmt 3 (.assign (.var "next") (.fieldAccess (.var "curr") "next")) st).bind
        fun r =>
          match r with
          | .normal st' => execStmt 3 (.seq (.free (.var "curr") 2) (.assign (.var "curr") (.var "next"))) st'
          | .returned v st' => some (.returned v st')) =
        some (.normal ((((st.updateVar "next" next).freeCells base 2).updateVar "curr" next))) := by
    rw [hAssignNext]
    exact hTail
  simpa [freeListLoopBody, execStmt] using hSeq

private theorem freeListLoopBody_executes_from_state_fuel
    (fuel : Nat) (st : CState) (base : Nat) (next : CVal)
    (hcurr : st.lookupVar "curr" = some (.ptr 0 (Int.ofNat base)))
    (hnext : st.heap.read (base + 1) = some next) :
    execStmt (fuel + 4) freeListLoopBody st =
      some (.normal ((((st.updateVar "next" next).freeCells base 2).updateVar "curr" next))) := by
  have hAssignNext :
      execStmt (fuel + 3) (.assign (.var "next") (.fieldAccess (.var "curr") "next")) st =
        some (.normal (st.updateVar "next" next)) :=
    freeList_assign_next_exec_fuel fuel st base next hcurr hnext
  have hFree :
      execStmt (fuel + 2) (.free (.var "curr") 2) (st.updateVar "next" next) =
        some (.normal ((st.updateVar "next" next).freeCells base 2)) :=
    freeList_free_curr_exec_fuel fuel st base next hcurr
  have hAssignCurr :
      execStmt (fuel + 2) (.assign (.var "curr") (.var "next")) (((st.updateVar "next" next).freeCells base 2)) =
        some (.normal ((((st.updateVar "next" next).freeCells base 2).updateVar "curr" next))) :=
    freeList_assign_curr_exec_fuel fuel st base next
  have hTail :
      execStmt (fuel + 3) (.seq (.free (.var "curr") 2) (.assign (.var "curr") (.var "next"))) (st.updateVar "next" next) =
        some (.normal ((((st.updateVar "next" next).freeCells base 2).updateVar "curr" next))) := by
    have hSeq :
        ((execStmt (fuel + 2) (.free (.var "curr") 2) (st.updateVar "next" next)).bind
          fun r =>
            match r with
            | .normal st' => execStmt (fuel + 2) (.assign (.var "curr") (.var "next")) st'
            | .returned v st' => some (.returned v st')) =
          some (.normal ((((st.updateVar "next" next).freeCells base 2).updateVar "curr" next))) := by
      rw [hFree]
      exact hAssignCurr
    simpa [execStmt] using hSeq
  have hSeq :
      ((execStmt (fuel + 3) (.assign (.var "next") (.fieldAccess (.var "curr") "next")) st).bind
        fun r =>
          match r with
          | .normal st' => execStmt (fuel + 3) (.seq (.free (.var "curr") 2) (.assign (.var "curr") (.var "next"))) st'
          | .returned v st' => some (.returned v st')) =
        some (.normal ((((st.updateVar "next" next).freeCells base 2).updateVar "curr" next))) := by
    rw [hAssignNext]
    exact hTail
  simpa [freeListLoopBody, execStmt] using hSeq

private theorem freeListLoopBody_preserves_tail
    (st : CState) (addr : Nat) (x : Int) (xs : List Int)
    (hcurr : st.lookupVar "curr" = some (.ptr 0 (Int.ofNat (Nat.succ addr))))
    (hsll : sll_s (.ptr 0 (Int.ofNat (Nat.succ addr))) (x :: xs) st) :
    ∃ next,
      execStmt 4 freeListLoopBody st =
        some (.normal ((((st.updateVar "next" next).freeCells (Nat.succ addr) 2).updateVar "curr" next))) ∧
      sll_s next xs ((((st.updateVar "next" next).freeCells (Nat.succ addr) 2).updateVar "curr" next)) := by
  rcases (sll_s_cons_iff addr x xs st).mp hsll with
    ⟨next, _hdata, hnext, hrest, hnotData, hnotNext⟩
  refine ⟨next, ?_, ?_⟩
  · exact freeListLoopBody_executes_from_state st (Nat.succ addr) next hcurr hnext
  · have hrest1 : sll_s next xs (st.updateVar "next" next) := by
      exact sll_s_updateVar_preserves next xs st "next" next hrest
    have hnotData1 : Nat.succ addr ∉ sll_s_addrs next xs (st.updateVar "next" next) := by
      simpa [sll_s_addrs_updateVar] using hnotData
    have hnotNext1 : Nat.succ addr + 1 ∉ sll_s_addrs next xs (st.updateVar "next" next) := by
      simpa [sll_s_addrs_updateVar] using hnotNext
    have hrest2 : sll_s next xs ((st.updateVar "next" next).freeCells (Nat.succ addr) 2) := by
      exact sll_s_freeCells_preserves next xs (st.updateVar "next" next) hrest1 hnotData1 hnotNext1
    exact sll_s_updateVar_preserves next xs (((st.updateVar "next" next).freeCells (Nat.succ addr) 2)) "curr" next hrest2

private theorem freeListLoopBody_preserves_tail_fuel
    (fuel : Nat) (st : CState) (addr : Nat) (x : Int) (xs : List Int)
    (hcurr : st.lookupVar "curr" = some (.ptr 0 (Int.ofNat (Nat.succ addr))))
    (hsll : sll_s (.ptr 0 (Int.ofNat (Nat.succ addr))) (x :: xs) st) :
    ∃ next,
      execStmt (fuel + 4) freeListLoopBody st =
        some (.normal ((((st.updateVar "next" next).freeCells (Nat.succ addr) 2).updateVar "curr" next))) ∧
      sll_s next xs ((((st.updateVar "next" next).freeCells (Nat.succ addr) 2).updateVar "curr" next)) := by
  rcases (sll_s_cons_iff addr x xs st).mp hsll with
    ⟨next, _hdata, hnext, hrest, hnotData, hnotNext⟩
  refine ⟨next, ?_, ?_⟩
  · exact freeListLoopBody_executes_from_state_fuel fuel st (Nat.succ addr) next hcurr hnext
  · have hrest1 : sll_s next xs (st.updateVar "next" next) := by
      exact sll_s_updateVar_preserves next xs st "next" next hrest
    have hnotData1 : Nat.succ addr ∉ sll_s_addrs next xs (st.updateVar "next" next) := by
      simpa [sll_s_addrs_updateVar] using hnotData
    have hnotNext1 : Nat.succ addr + 1 ∉ sll_s_addrs next xs (st.updateVar "next" next) := by
      simpa [sll_s_addrs_updateVar] using hnotNext
    have hrest2 : sll_s next xs ((st.updateVar "next" next).freeCells (Nat.succ addr) 2) := by
      exact sll_s_freeCells_preserves next xs (st.updateVar "next" next) hrest1 hnotData1 hnotNext1
    exact sll_s_updateVar_preserves next xs (((st.updateVar "next" next).freeCells (Nat.succ addr) 2)) "curr" next hrest2

private theorem freeList_loopFree : LoopFree freeListLoopBody := by
  simp [freeListLoopBody, LoopFree]

private theorem freeList_noReturn : NoReturn freeListLoopBody := by
  simp [freeListLoopBody, NoReturn]

private theorem freedAt_insert_head
    (full rem : Finset Nat) (st : CState) (addr : Nat)
    (hfreed : freedAt (full \ insert addr (insert (addr + 1) rem)) st)
    (hdata : st.heap.read addr = none)
    (hnext : st.heap.read (addr + 1) = none) :
    freedAt (full \ rem) st := by
  intro z hz
  rcases Finset.mem_sdiff.mp hz with ⟨hzFull, hzNotRem⟩
  by_cases hz0 : z = addr
  · subst hz0
    exact hdata
  · by_cases hz1 : z = addr + 1
    · subst hz1
      exact hnext
    · exact hfreed z (Finset.mem_sdiff.mpr ⟨hzFull, by simp [hz0, hz1, hzNotRem]⟩)

private theorem freeList_loop_from_state
    (head curr : CVal) (rem : List Int) (fullAddrs : Finset Nat) (st : CState)
    (hhead : st.lookupVar "head" = some head)
    (hcurr : st.lookupVar "curr" = some curr)
    (hsll : sll_s curr rem st)
    (hfreed : freedAt (fullAddrs \ sll_s_addrs curr rem st) st) :
    swhileWP rem.length freeListCond (freeListInv head fullAddrs)
      freeListLoopBody (freeListLoopPost head fullAddrs) st := by
  induction rem generalizing curr st with
  | nil =>
      have hcurrNull : curr = .null := sll_s_nil_ptr_eq_null hsll
      subst hcurrNull
      have hInv : freeListInv head fullAddrs st := by
        refine ⟨.null, [], hhead, hcurr, hsll, ?_⟩
        simpa [sll_s_addrs] using hfreed
      have hEvalCond : evalExpr freeListCond st = some (.int 0) :=
        freeListCond_eval_null st hcurr
      have hPost : freeListLoopPost head fullAddrs CVal.undef st := by
        refine ⟨hhead, hcurr, ?_⟩
        simpa [sll_s_addrs] using hfreed
      simpa [swhileWP, hEvalCond, isTruthy] using And.intro hInv hPost
  | cons x rest ih =>
      have hInv : freeListInv head fullAddrs st := by
        exact ⟨curr, x :: rest, hhead, hcurr, hsll, hfreed⟩
      have hcurrTruthy : isTruthy curr = true := sll_s_nonempty_truthy hsll
      rcases sll_s_head_truthy hcurrTruthy hsll with
        ⟨addr, x', rest', next, hptrBase, hshape, hdata, hnext, hrest, hnotData, hnotNext⟩
      injection hshape with hxEq hrestEq
      subst hxEq hrestEq
      have hcurrEq : curr = .ptr 0 (Int.ofNat (Nat.succ addr)) := ptr_eq_of_ptrBase_some hptrBase
      subst hcurrEq
      have hcurrPtr : st.lookupVar "curr" = some (.ptr 0 (Int.ofNat (Nat.succ addr))) := hcurr
      have hEvalCond : evalExpr freeListCond st = some (.int 1) :=
        freeListCond_eval_ptr st (Nat.succ addr) hcurrPtr
      let st1 := st.updateVar "next" next
      let st2 := st1.freeCells (Nat.succ addr) 2
      let st3 := st2.updateVar "curr" next
      have hhead3 : st3.lookupVar "head" = some head := by
        calc
          st3.lookupVar "head" = st2.lookupVar "head" := by
            simpa [st3] using lookupVar_updateVar_ne st2 "curr" "head" next
              (by decide : "head" ≠ "curr")
          _ = st1.lookupVar "head" := by rfl
          _ = st.lookupVar "head" := by
            simpa [st1] using lookupVar_updateVar_ne st "next" "head" next
              (by decide : "head" ≠ "next")
          _ = some head := hhead
      have hcurr3 : st3.lookupVar "curr" = some next := by
        simpa [st3] using lookupVar_updateVar_eq st2 "curr" next
      have hnotData1 : Nat.succ addr ∉ sll_s_addrs next rest st1 := by
        simpa [st1, sll_s_addrs_updateVar] using hnotData
      have hnotNext1 : Nat.succ addr + 1 ∉ sll_s_addrs next rest st1 := by
        simpa [st1, sll_s_addrs_updateVar] using hnotNext
      have hrest1 : sll_s next rest st1 := by
        exact sll_s_updateVar_preserves next rest st "next" next hrest
      have hrest2 : sll_s next rest st2 := by
        exact sll_s_freeCells_preserves next rest st1 hrest1 hnotData1 hnotNext1
      have hrest3 : sll_s next rest st3 := by
        exact sll_s_updateVar_preserves next rest st2 "curr" next hrest2
      have hTailAddrs : sll_s_addrs next rest st3 = sll_s_addrs next rest st := by
        calc
          sll_s_addrs next rest st3 = sll_s_addrs next rest st2 := by
            simpa [st3] using sll_s_addrs_updateVar next rest st2 "curr" next
          _ = sll_s_addrs next rest st1 := by
            simpa [st2] using sll_s_addrs_freeCells_eq next rest st1 hnotData1 hnotNext1
          _ = sll_s_addrs next rest st := by
            simpa [st1] using sll_s_addrs_updateVar next rest st "next" next
      have hOldAddrs :
          sll_s_addrs (.ptr 0 (Int.ofNat (Nat.succ addr))) (x :: rest) st =
            insert (Nat.succ addr) (insert (Nat.succ addr + 1) (sll_s_addrs next rest st)) := by
        have hnonneg : 0 ≤ (Int.ofNat (Nat.succ addr) : Int) := Int.natCast_nonneg _
        change
          (match (if 0 ≤ (Int.ofNat (Nat.succ addr) : Int) then some addr else none) with
            | some a =>
                insert (Nat.succ a)
                  (insert (Nat.succ a + 1)
                    (match st.heap.read (Nat.succ a + 1) with
                    | some next' => sll_s_addrs next' rest st
                    | none => ∅))
            | none => ∅) =
            insert (Nat.succ addr) (insert (Nat.succ addr + 1) (sll_s_addrs next rest st))
        rw [if_pos hnonneg]
        simp [hnext]
      have hbaseInOld :
          Nat.succ addr ∈ sll_s_addrs (.ptr 0 (Int.ofNat (Nat.succ addr))) (x :: rest) st := by
        rw [hOldAddrs]
        simp
      have hnextInOld :
          Nat.succ addr + 1 ∈ sll_s_addrs (.ptr 0 (Int.ofNat (Nat.succ addr))) (x :: rest) st := by
        rw [hOldAddrs]
        simp
      have hbaseNotFreed :
          Nat.succ addr ∉ fullAddrs \ sll_s_addrs (.ptr 0 (Int.ofNat (Nat.succ addr))) (x :: rest) st := by
        intro hmem
        exact (Finset.mem_sdiff.mp hmem).2 hbaseInOld
      have hnextNotFreed :
          Nat.succ addr + 1 ∉ fullAddrs \ sll_s_addrs (.ptr 0 (Int.ofNat (Nat.succ addr))) (x :: rest) st := by
        intro hmem
        exact (Finset.mem_sdiff.mp hmem).2 hnextInOld
      have hfreed1 :
          freedAt (fullAddrs \ sll_s_addrs (.ptr 0 (Int.ofNat (Nat.succ addr))) (x :: rest) st) st1 := by
        exact freedAt_updateVar _ st "next" next hfreed
      have hfreed2 :
          freedAt (fullAddrs \ sll_s_addrs (.ptr 0 (Int.ofNat (Nat.succ addr))) (x :: rest) st) st2 := by
        exact freedAt_freeCells_preserves
          (fullAddrs \ sll_s_addrs (.ptr 0 (Int.ofNat (Nat.succ addr))) (x :: rest) st)
          st1 (Nat.succ addr) hfreed1 hbaseNotFreed hnextNotFreed
      have hfreed3 :
          freedAt (fullAddrs \ sll_s_addrs (.ptr 0 (Int.ofNat (Nat.succ addr))) (x :: rest) st) st3 := by
        exact freedAt_updateVar _ st2 "curr" next hfreed2
      have hfreedStruct :
          freedAt (fullAddrs \ insert (Nat.succ addr)
            (insert (Nat.succ addr + 1) (sll_s_addrs next rest st3))) st3 := by
        rw [hOldAddrs] at hfreed3
        simpa [hTailAddrs] using hfreed3
      have hdataNone : st3.heap.read (Nat.succ addr) = none := by
        simpa [st3, st2] using freeCells_read_eq_none st1 (Nat.succ addr)
      have hnextNone : st3.heap.read (Nat.succ addr + 1) = none := by
        simpa [st3, st2] using freeCells_read_next_eq_none st1 (Nat.succ addr)
      have hfreedNew : freedAt (fullAddrs \ sll_s_addrs next rest st3) st3 := by
        exact freedAt_insert_head fullAddrs (sll_s_addrs next rest st3) st3 (Nat.succ addr)
          hfreedStruct hdataNone hnextNone
      have hLoopTail :
          swhileWP rest.length freeListCond (freeListInv head fullAddrs)
            freeListLoopBody (freeListLoopPost head fullAddrs) st3 := by
        exact ih next st3 hhead3 hcurr3 hrest3 hfreedNew
      have hEvalNextField :
          evalExpr (.fieldAccess (.var "curr") "next") st = some next :=
        freeList_eval_next_field st (Nat.succ addr) next hcurrPtr hnext
      have hEvalCurr1 :
          evalExpr (.var "curr") st1 = some (.ptr 0 (Int.ofNat (Nat.succ addr))) := by
        simpa [st1] using
          freeList_eval_curr_after_set_next st (.ptr 0 (Int.ofNat (Nat.succ addr))) next hcurrPtr
      have hResolve1 :
          st1.resolvePtr { block := 0, offset := Int.ofNat (Nat.succ addr) } = some (Nat.succ addr) :=
        freeList_resolve_curr_after_set_next st (Nat.succ addr) next
      have hLookupNext2 : st2.lookupVar "next" = some next := by
        simpa [st2] using freeList_lookup_next_after_free st (Nat.succ addr) next
      have hEvalNext2 : evalExpr (.var "next") st2 = some next :=
        freeList_eval_next_after_free st (Nat.succ addr) next hLookupNext2
      have hAssignAfterFree :
          swp (.assign (.var "curr") (.var "next"))
            (fun _ =>
              swhileWP rest.length freeListCond (freeListInv head fullAddrs)
                freeListLoopBody (freeListLoopPost head fullAddrs)) st2 := by
        simpa [swp, hEvalNext2, st3] using hLoopTail
      have hTailBody :
          swp (.seq (.free (.var "curr") 2) (.assign (.var "curr") (.var "next")))
            (fun _ =>
              swhileWP rest.length freeListCond (freeListInv head fullAddrs)
                freeListLoopBody (freeListLoopPost head fullAddrs)) st1 := by
        change swp (.free (.var "curr") 2)
          (fun _ =>
            swp (.assign (.var "curr") (.var "next"))
              (fun _ =>
                swhileWP rest.length freeListCond (freeListInv head fullAddrs)
                  freeListLoopBody (freeListLoopPost head fullAddrs))) st1
        simp [swp, hEvalCurr1]
        exact ⟨Nat.succ addr, hResolve1, hAssignAfterFree⟩
      have hBody :
          swp freeListLoopBody
            (fun _ =>
              swhileWP rest.length freeListCond (freeListInv head fullAddrs)
                freeListLoopBody (freeListLoopPost head fullAddrs)) st := by
        simpa [freeListLoopBody, swp, hEvalNextField, st1] using hTailBody
      simpa [swhileWP, hEvalCond, isTruthy] using And.intro hInv hBody

theorem freeList_correct (xs : List Int) (head : CVal) :
    ∀ st,
      st.lookupVar "head" = some head →
      sll_s head xs st →
      ∃ st',
        execStmt (swhileFuel freeListLoopBody xs.length + 1) freeListBody st = some (.normal st') ∧
        st'.lookupVar "head" = some head ∧
        st'.lookupVar "curr" = some .null ∧
        freedAt (sll_s_addrs head xs st) st' := by
  intro st hhead hsll
  let fullAddrs := sll_s_addrs head xs st
  let st1 := st.updateVar "curr" head
  have hhead1 : st1.lookupVar "head" = some head := by
    calc
      st1.lookupVar "head" = st.lookupVar "head" := by
        simpa [st1] using lookupVar_updateVar_ne st "curr" "head" head
          (by decide : "head" ≠ "curr")
      _ = some head := hhead
  have hcurr1 : st1.lookupVar "curr" = some head := by
    simpa [st1] using lookupVar_updateVar_eq st "curr" head
  have hsll1 : sll_s head xs st1 := by
    exact sll_s_updateVar_preserves head xs st "curr" head hsll
  have haddrs1 : sll_s_addrs head xs st1 = fullAddrs := by
    simpa [fullAddrs, st1] using sll_s_addrs_updateVar head xs st "curr" head
  have hfreed1 : freedAt (fullAddrs \ sll_s_addrs head xs st1) st1 := by
    simpa [freedAt, haddrs1]
  have hLoopWP :
      swhileWP xs.length freeListCond (freeListInv head fullAddrs)
        freeListLoopBody (freeListLoopPost head fullAddrs) st1 := by
    exact freeList_loop_from_state head head xs fullAddrs st1 hhead1 hcurr1 hsll1 hfreed1
  have hLoopExec :
      ∃ stLoop,
        execStmt (swhileFuel freeListLoopBody xs.length)
          (.whileInv freeListCond HProp.htrue freeListLoopBody) st1 = some (.normal stLoop) ∧
        freeListLoopPost head fullAddrs CVal.undef stLoop := by
    exact swhileWP_sound freeListCond (freeListInv head fullAddrs) HProp.htrue
      freeListLoopBody freeList_loopFree freeList_noReturn hLoopWP
  rcases hLoopExec with ⟨stLoop, hExecLoop, hPostLoop⟩
  rcases hPostLoop with ⟨hheadLoop, hcurrLoop, hfreedLoop⟩
  have hEvalHead : evalExpr (.var "head") st = some head := by
    simpa [evalExpr, evalStaticExpr] using hhead
  let loopFuel := swhileFuel freeListLoopBody xs.length
  have hLoopFuelSucc : loopFuel = Nat.succ (stmtDepth freeListLoopBody + xs.length) := by
    simp [loopFuel, swhileFuel, Nat.add_assoc]
  have hExecBody :
      execStmt (loopFuel + 1) freeListBody st = some (.normal stLoop) := by
    change execStmt (Nat.succ loopFuel)
      (.seq (.assign (.var "curr") (.var "head"))
        (.whileInv freeListCond HProp.htrue freeListLoopBody)) st =
      some (.normal stLoop)
    have hExecStart :
        execStmt loopFuel (.assign (.var "curr") (.var "head")) st =
          some (.normal st1) := by
      rw [hLoopFuelSucc]
      simpa [execStmt, hEvalHead, st1]
    have hSeq :
        ((execStmt loopFuel (.assign (.var "curr") (.var "head")) st).bind
          fun r =>
            match r with
            | .normal st' => execStmt loopFuel (.whileInv freeListCond HProp.htrue freeListLoopBody) st'
            | .returned v st' => some (.returned v st')) =
          some (.normal stLoop) := by
      rw [hExecStart]
      exact hExecLoop
    simpa [freeListBody, execStmt] using hSeq
  refine ⟨stLoop, hExecBody, hheadLoop, hcurrLoop, ?_⟩
  simpa [fullAddrs] using hfreedLoop

def freeListInit : CState :=
  { heap := ((((Heap.empty.write 300 (.int 7)).write 301 (.ptr 0 302)).write 302 (.int 9)).write 303 .null)
    env := [("head", .ptr 0 300)]
    nextAddr := 400 }

def freeListFinal : CState :=
  { heap := Heap.empty
    env := [("curr", .null), ("next", .null), ("head", .ptr 0 300)]
    nextAddr := 400 }

theorem freeList_executes :
    execStmt 12 freeListBody freeListInit = some (.normal freeListFinal) := by
  native_decide

theorem freeList_verified :
    ∃ st',
      execStmt 12 freeListBody freeListInit = some (.normal st') ∧
      st'.heap.read 300 = none ∧
      st'.heap.read 301 = none ∧
      st'.heap.read 302 = none ∧
      st'.heap.read 303 = none := by
  refine ⟨freeListFinal, freeList_executes, ?_, ?_, ?_, ?_⟩ <;>
    simp [freeListFinal, Heap.read, Heap.empty]

theorem freeList_seed_verified :
    swp (.assign (.var "curr") (.var "head"))
      (fun _ st => st.lookupVar "curr" = some (.ptr 0 300))
      freeListInit := by
  xstep
  simp [freeListInit, CState.lookupVar, CState.updateVar]

end HeytingLean.LeanCP.Examples
