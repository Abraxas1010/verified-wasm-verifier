import HeytingLean.LeanCP.Examples.TreeInsert
import HeytingLean.LeanCP.Lang.CSemanticsDecEq
import HeytingLean.LeanCP.Core.VarLemmas
import HeytingLean.LeanCP.Tactics.Forward

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

set_option linter.unnecessarySimpa false

/-- Read-only state predicate for a single tree node cell layout. -/
def treeNodeAt_s (base : Nat) (value : Int) (left right : CVal) : SProp := fun st =>
  st.heap.read base = some (.int value) ∧
  st.heap.read (base + 1) = some left ∧
  st.heap.read (base + 2) = some right

def treeInsertCallPtr (st : CState) : PtrVal :=
  { block := st.mem.nextBlock, offset := 0 }

def treeInsertCallAlloc (st : CState) (base : Nat) : FlatAlloc :=
  { base := base, block := st.mem.nextBlock, cells := 3 }

def treeInsertBaseCaseAllocState (st : CState) : CState :=
  st.allocCells "node" 3

def treeInsertBaseCaseDataState (st : CState) (base : Nat) (value : Int) : CState :=
  let st1 := treeInsertBaseCaseAllocState st
  st1.withHeap (st1.heap.write base (.int value))

def treeInsertBaseCaseLeftState (st : CState) (base : Nat) (value : Int) : CState :=
  let st2 := treeInsertBaseCaseDataState st base value
  st2.withHeap (st2.heap.write (base + 1) .null)

def treeInsertBaseCaseFinalState (st : CState) (base : Nat) (value : Int) : CState :=
  let st3 := treeInsertBaseCaseLeftState st base value
  st3.withHeap (st3.heap.write (base + 2) .null)

theorem treeInsert_base_executes_from_state (value : Int) (base : Nat) :
    ∀ st,
      st.lookupVar "root" = some .null →
      st.lookupVar "v" = some (.int value) →
      st.nextAddr = base →
      st.mem.nextBlock ≠ 0 →
      execStmt 12 bstInsertBaseCase st =
        some (.returned (CVal.ptrAddr (treeInsertCallPtr st)) (treeInsertBaseCaseFinalState st base value)) := by
  intro st hroot hv hbase hblock
  let ptr := treeInsertCallPtr st
  let block := st.mem.nextBlock
  let st1 := treeInsertBaseCaseAllocState st
  let st2 := treeInsertBaseCaseDataState st base value
  let st3 := treeInsertBaseCaseLeftState st base value
  let st4 := treeInsertBaseCaseFinalState st base value
  have hallocfresh :
      (st.mem.alloc 0 (Int.ofNat 3) .Freeable).1 = block := by
    simpa [block] using
      (Mem.alloc_fresh st.mem 0 (Int.ofNat 3) .Freeable
        ((st.mem.alloc 0 (Int.ofNat 3) .Freeable).1)
        ((st.mem.alloc 0 (Int.ofNat 3) .Freeable).2) rfl)
  have hallocfreshNat :
      (st.mem.alloc 0 3 .Freeable).1 = block := by
    simpa [block] using
      (Mem.alloc_fresh st.mem 0 3 .Freeable
        ((st.mem.alloc 0 3 .Freeable).1)
        ((st.mem.alloc 0 3 .Freeable).2) rfl)
  have hcond :
      evalExpr (.binop .eq (.var "root") .null) st = some (.int 1) := by
    simpa [evalExpr, evalStaticExpr, hroot] using
      (show evalBinOp .eq .null .null = some (.int 1) by rfl)
  have hv1 : st1.lookupVar "v" = some (.int value) := by
    simpa [st1, treeInsertBaseCaseAllocState, CState.lookupVar, CState.allocCells] using hv
  have hnode1 : st1.lookupVar "node" = some (CVal.ptrAddr ptr) := by
    simp [st1, ptr, block, treeInsertBaseCaseAllocState, treeInsertCallPtr,
      CState.lookupVar, CState.allocCells, CVal.ptrAddr, hallocfreshNat]
  have hnode2 : st2.lookupVar "node" = some (CVal.ptrAddr ptr) := by
    simpa [st2, treeInsertBaseCaseDataState, CState.lookupVar, CState.withHeap] using hnode1
  have hnode3 : st3.lookupVar "node" = some (CVal.ptrAddr ptr) := by
    simpa [st3, treeInsertBaseCaseLeftState, CState.lookupVar, CState.withHeap] using hnode2
  have hnode4 : st4.lookupVar "node" = some (CVal.ptrAddr ptr) := by
    simpa [st4, treeInsertBaseCaseFinalState, CState.lookupVar, CState.withHeap] using hnode3
  have hvEval : evalExpr (.var "v") st1 = some (.int value) := by
    simpa [evalExpr] using hv1
  have hnodeEval1 : evalExpr (.var "node") st1 = some (CVal.ptrAddr ptr) := by
    simpa [evalExpr] using hnode1
  have hnodeEval2 : evalExpr (.var "node") st2 = some (CVal.ptrAddr ptr) := by
    simpa [evalExpr] using hnode2
  have hnodeEval3 : evalExpr (.var "node") st3 = some (CVal.ptrAddr ptr) := by
    simpa [evalExpr] using hnode3
  have hnodeEval4 : evalExpr (.var "node") st4 = some (CVal.ptrAddr ptr) := by
    simpa [evalExpr] using hnode4
  have hfind1 :
      st1.findAllocByBlock block = some { base := base, block := block, cells := 3 } := by
    simp [st1, block, treeInsertBaseCaseAllocState, CState.findAllocByBlock,
      CState.allocCells, hbase, hallocfreshNat]
  have hresolveData : st1.resolvePtr ptr = some base := by
    simpa [ptr, block, hbase] using
      (CState.resolvePtr_tracked st1 { base := base, block := block, cells := 3 } 0
        hfind1 hblock (by decide : 0 < 3))
  have hwriteData : st1.writePtr ptr (.int value) = some st2 := by
    rw [CState.writePtr, hresolveData]
    change some (st1.withHeap (st1.heap.write base (.int value))) = some st2
    rfl
  have hfind2 :
      st2.findAllocByBlock block = some { base := base, block := block, cells := 3 } := by
    simp [st2, st1, block, treeInsertBaseCaseDataState, treeInsertBaseCaseAllocState,
      CState.findAllocByBlock, CState.allocCells, CState.withHeap, hbase, hallocfreshNat]
  have hresolveLeft :
      st2.resolvePtr { block := block, offset := 1 } = some (base + 1) := by
    simpa [block, hbase] using
      (CState.resolvePtr_tracked st2 { base := base, block := block, cells := 3 } 1
        hfind2 hblock (by decide : 1 < 3))
  have hwriteLeft : st2.writePtr { block := block, offset := 1 } .null = some st3 := by
    rw [CState.writePtr, hresolveLeft]
    change some (st2.withHeap (st2.heap.write (base + 1) .null)) = some st3
    rfl
  have hfind3 :
      st3.findAllocByBlock block = some { base := base, block := block, cells := 3 } := by
    simp [st3, st2, st1, block, treeInsertBaseCaseLeftState, treeInsertBaseCaseDataState,
      treeInsertBaseCaseAllocState, CState.findAllocByBlock, CState.allocCells,
      CState.withHeap, hbase, hallocfreshNat]
  have hresolveRight :
      st3.resolvePtr { block := block, offset := 2 } = some (base + 2) := by
    simpa [block, hbase] using
      (CState.resolvePtr_tracked st3 { base := base, block := block, cells := 3 } 2
        hfind3 hblock (by decide : 2 < 3))
  have hwriteRight : st3.writePtr { block := block, offset := 2 } .null = some st4 := by
    rw [CState.writePtr, hresolveRight]
    change some (st3.withHeap (st3.heap.write (base + 2) .null)) = some st4
    rfl
  have hExecAlloc :
      execStmt 10 (.alloc "node" 3) st = some (.normal st1) := by
    simp [execStmt, st1, treeInsertBaseCaseAllocState]
  have hExecAssignData :
      execStmt 9 (.assign (.fieldAccess (.var "node") "data") (.var "v")) st1 =
        some (.normal st2) := by
    simp [execStmt, hvEval, hnode1, CVal.ptrAddr]
    simpa [ptr, block, PtrVal.addOffset, Addr.addOffset, fieldOffset] using hwriteData
  have hMapWriteLeft :
      Option.map ExecResult.normal (st2.writePtr { block := block, offset := 1 } .null) =
        some (.normal st3) := by
    rw [hwriteLeft]
    rfl
  have hExecAssignLeft :
      execStmt 8 (.assign (.fieldAccess (.var "node") "left") .null) st2 =
        some (.normal st3) := by
    simp [execStmt, hnode2, CVal.ptrAddr]
    simpa [evalExpr, evalStaticExpr, ptr, block, PtrVal.addOffset, Addr.addOffset, fieldOffset] using hMapWriteLeft
  have hMapWriteRight :
      Option.map ExecResult.normal (st3.writePtr { block := block, offset := 2 } .null) =
        some (.normal st4) := by
    rw [hwriteRight]
    rfl
  have hExecAssignRight :
      execStmt 7 (.assign (.fieldAccess (.var "node") "right") .null) st3 =
        some (.normal st4) := by
    simp [execStmt, hnode3, CVal.ptrAddr]
    simpa [evalExpr, evalStaticExpr, ptr, block, PtrVal.addOffset, Addr.addOffset, fieldOffset] using hMapWriteRight
  have hExecRetNode :
      execStmt 7 (.ret (.var "node")) st4 =
        some (.returned (CVal.ptrAddr ptr) st4) := by
    simp [execStmt, hnodeEval4]
  have hRetNodeRaw :
      (st4.lookupVar "node").bind (fun v => some (ExecResult.returned v st4)) =
        some (ExecResult.returned (CVal.ptrAddr ptr) st4) := by
    simpa [execStmt] using hExecRetNode
  have hAssignRightRaw :
      ((evalExpr .null st3).bind fun v =>
          (st3.lookupVar "node").bind fun pv =>
            match pv with
            | .ptr block offset =>
                (PtrVal.addOffset { block := block, offset := offset } (Int.ofNat (fieldOffset "right"))).bind
                  fun slot => Option.map ExecResult.normal (st3.writePtr slot v)
            | _ => none) =
        some (.normal st4) := by
    simpa [execStmt] using hExecAssignRight
  have hExecAfterRight :
      execStmt 8
          (.seq (.assign (.fieldAccess (.var "node") "right") .null) (.ret (.var "node")))
          st3 =
        some (.returned (CVal.ptrAddr ptr) st4) := by
    have hSeqRaw :
        (((evalExpr .null st3).bind fun v =>
            (st3.lookupVar "node").bind fun pv =>
              match pv with
              | .ptr block offset =>
                  (PtrVal.addOffset { block := block, offset := offset } (Int.ofNat (fieldOffset "right"))).bind
                    fun slot => Option.map ExecResult.normal (st3.writePtr slot v)
              | _ => none).bind
          fun __do_lift =>
            match __do_lift with
            | ExecResult.normal st' => (st'.lookupVar "node").bind (fun v => some (ExecResult.returned v st'))
            | ExecResult.returned v st' => some (ExecResult.returned v st')) =
          some (ExecResult.returned (CVal.ptrAddr ptr) st4) := by
      rw [hAssignRightRaw]
      exact hRetNodeRaw
    simpa [execStmt] using hSeqRaw
  have hAssignLeftRaw :
      ((evalExpr .null st2).bind fun v =>
          (st2.lookupVar "node").bind fun pv =>
            match pv with
            | .ptr block offset =>
                (PtrVal.addOffset { block := block, offset := offset } (Int.ofNat (fieldOffset "left"))).bind
                  fun slot => Option.map ExecResult.normal (st2.writePtr slot v)
            | _ => none) =
        some (.normal st3) := by
    simpa [execStmt] using hExecAssignLeft
  have hExecAfterLeft :
      execStmt 9
          (.seq (.assign (.fieldAccess (.var "node") "left") .null)
            (.seq (.assign (.fieldAccess (.var "node") "right") .null) (.ret (.var "node"))))
          st2 =
        some (.returned (CVal.ptrAddr ptr) st4) := by
    have hSeqRaw :
        (((evalExpr .null st2).bind fun v =>
            (st2.lookupVar "node").bind fun pv =>
              match pv with
              | .ptr block offset =>
                  (PtrVal.addOffset { block := block, offset := offset } (Int.ofNat (fieldOffset "left"))).bind
                    fun slot => Option.map ExecResult.normal (st2.writePtr slot v)
              | _ => none).bind
          fun __do_lift =>
            match __do_lift with
            | ExecResult.normal st' =>
                execStmt 8 (.seq (.assign (.fieldAccess (.var "node") "right") .null) (.ret (.var "node"))) st'
            | ExecResult.returned v st' => some (ExecResult.returned v st')) =
          some (ExecResult.returned (CVal.ptrAddr ptr) st4) := by
      rw [hAssignLeftRaw]
      exact hExecAfterRight
    simpa [execStmt] using hSeqRaw
  have hAssignDataRaw :
      ((st1.lookupVar "v").bind fun v =>
          (st1.lookupVar "node").bind fun pv =>
            match pv with
            | .ptr block offset =>
                (PtrVal.addOffset { block := block, offset := offset } (Int.ofNat (fieldOffset "data"))).bind
                  fun slot => Option.map ExecResult.normal (st1.writePtr slot v)
            | _ => none) =
        some (.normal st2) := by
    simpa [execStmt] using hExecAssignData
  have hExecAfterData :
      execStmt 10
          (.seq (.assign (.fieldAccess (.var "node") "data") (.var "v"))
            (.seq (.assign (.fieldAccess (.var "node") "left") .null)
              (.seq (.assign (.fieldAccess (.var "node") "right") .null) (.ret (.var "node")))))
          st1 =
        some (.returned (CVal.ptrAddr ptr) st4) := by
    have hSeqRaw :
        (((st1.lookupVar "v").bind fun v =>
            (st1.lookupVar "node").bind fun pv =>
              match pv with
              | .ptr block offset =>
                  (PtrVal.addOffset { block := block, offset := offset } (Int.ofNat (fieldOffset "data"))).bind
                    fun slot => Option.map ExecResult.normal (st1.writePtr slot v)
              | _ => none).bind
          fun __do_lift =>
            match __do_lift with
            | ExecResult.normal st' =>
                execStmt 9
                  (.seq (.assign (.fieldAccess (.var "node") "left") .null)
                    (.seq (.assign (.fieldAccess (.var "node") "right") .null) (.ret (.var "node"))))
                  st'
            | ExecResult.returned v st' => some (ExecResult.returned v st')) =
          some (ExecResult.returned (CVal.ptrAddr ptr) st4) := by
      rw [hAssignDataRaw]
      exact hExecAfterLeft
    simpa [execStmt] using hSeqRaw
  have hExecBranch :
      execStmt 11
          (.seq (.alloc "node" 3)
            (.seq (.assign (.fieldAccess (.var "node") "data") (.var "v"))
              (.seq (.assign (.fieldAccess (.var "node") "left") .null)
                (.seq (.assign (.fieldAccess (.var "node") "right") .null) (.ret (.var "node"))))))
          st =
        some (.returned (CVal.ptrAddr ptr) st4) := by
    have hSeqRaw :
        (match execStmt 10 (.alloc "node" 3) st with
        | some (.normal st') =>
            execStmt 10
              (.seq (.assign (.fieldAccess (.var "node") "data") (.var "v"))
                (.seq (.assign (.fieldAccess (.var "node") "left") .null)
                  (.seq (.assign (.fieldAccess (.var "node") "right") .null) (.ret (.var "node")))))
              st'
        | some (.returned v st') => some (.returned v st')
        | none => none) =
          some (.returned (CVal.ptrAddr ptr) st4) := by
      rw [hExecAlloc]
      exact hExecAfterData
    simpa [execStmt] using hSeqRaw
  simpa [bstInsertBaseCase, execStmt, hcond, isTruthy] using hExecBranch

theorem treeInsert_correct (value : Int) (base : Nat) :
    ∀ st,
      st.lookupVar "root" = some .null →
      st.lookupVar "v" = some (.int value) →
      st.nextAddr = base →
      st.mem.nextBlock ≠ 0 →
      ∃ st',
        execStmt 12 bstInsertBaseCase st =
          some (.returned (CVal.ptrAddr (treeInsertCallPtr st)) st') ∧
        st'.lookupVar "root" = some .null ∧
        st'.lookupVar "v" = some (.int value) ∧
        st'.lookupVar "node" = some (CVal.ptrAddr (treeInsertCallPtr st)) ∧
        treeNodeAt_s base value .null .null st' := by
  intro st hroot hv hbase hblock
  refine ⟨treeInsertBaseCaseFinalState st base value, ?_, ?_, ?_, ?_, ?_⟩
  · exact treeInsert_base_executes_from_state value base st hroot hv hbase hblock
  · calc
      (treeInsertBaseCaseFinalState st base value).lookupVar "root" =
          (treeInsertBaseCaseAllocState st).lookupVar "root" := by
            simp [treeInsertBaseCaseFinalState, treeInsertBaseCaseLeftState,
              treeInsertBaseCaseDataState, treeInsertBaseCaseAllocState, CState.lookupVar, CState.withHeap]
      _ = some .null := by
        simpa [treeInsertBaseCaseAllocState, CState.lookupVar, CState.allocCells] using hroot
  · calc
      (treeInsertBaseCaseFinalState st base value).lookupVar "v" =
          (treeInsertBaseCaseAllocState st).lookupVar "v" := by
            simp [treeInsertBaseCaseFinalState, treeInsertBaseCaseLeftState,
              treeInsertBaseCaseDataState, treeInsertBaseCaseAllocState, CState.lookupVar, CState.withHeap]
      _ = some (.int value) := by
        simpa [treeInsertBaseCaseAllocState, CState.lookupVar, CState.allocCells] using hv
  · have hallocfreshNat :
        (st.mem.alloc 0 3 .Freeable).1 = st.mem.nextBlock := by
      simpa using
        (Mem.alloc_fresh st.mem 0 3 .Freeable
          ((st.mem.alloc 0 3 .Freeable).1)
          ((st.mem.alloc 0 3 .Freeable).2) rfl)
    simp [treeInsertBaseCaseFinalState, treeInsertBaseCaseLeftState, treeInsertBaseCaseDataState,
      treeInsertBaseCaseAllocState, treeInsertCallPtr, CState.lookupVar, CState.withHeap,
      CState.allocCells, CVal.ptrAddr, hallocfreshNat]
  · simp [treeNodeAt_s, treeInsertBaseCaseFinalState, treeInsertBaseCaseLeftState,
      treeInsertBaseCaseDataState, treeInsertBaseCaseAllocState, CState.withHeap, CState.allocCells,
      Heap.read, Heap.write]

def treeInsertInit : CState :=
  { heap := Heap.empty
    env := [("root", .null), ("v", .int 5)]
    nextAddr := 400 }

def treeInsertBlock : Block :=
  ((heapToMem Heap.empty).alloc 0 (Int.ofNat 3) .Freeable).1

def treeInsertPtr : PtrVal := { block := treeInsertBlock, offset := 0 }

def treeInsertAlloc : FlatAlloc := { base := 400, block := treeInsertBlock, cells := 3 }

def treeInsertFinal : CState :=
  let heap := (((Heap.empty.write 400 (.int 5)).write 401 .null).write 402 .null)
  { heap := heap
    env := [("node", CVal.ptrAddr treeInsertPtr), ("root", .null), ("v", .int 5)]
    nextAddr := 403
    mem := CState.syncMem heap [treeInsertAlloc] (((heapToMem Heap.empty).alloc 0 (Int.ofNat 3) .Freeable).2.nextBlock)
    allocs := [treeInsertAlloc] }

theorem treeInsert_executes :
    execStmt 12 bstInsertBaseCase treeInsertInit =
      some (.returned (CVal.ptrAddr treeInsertPtr) treeInsertFinal) := by
  native_decide

theorem treeInsert_verified :
    ∃ st',
      execStmt 12 bstInsertBaseCase treeInsertInit =
        some (.returned (CVal.ptrAddr treeInsertPtr) st') ∧
      st'.heap.read 400 = some (.int 5) ∧
      st'.heap.read 401 = some .null ∧
      st'.heap.read 402 = some .null := by
  refine ⟨treeInsertFinal, treeInsert_executes, ?_, ?_, ?_⟩ <;>
    simp [treeInsertFinal]

theorem treeInsert_forward_verified :
    swp (.alloc "node" 3)
      (fun _ st => st.lookupVar "node" = some (CVal.ptrAddr treeInsertPtr))
      treeInsertInit := by
  simp [swp, treeInsertInit, treeInsertPtr, treeInsertBlock, CVal.ptrAddr,
    CState.lookupVar, CState.allocCells, CState.syncMem, CState.allocContents]

end HeytingLean.LeanCP.Examples
