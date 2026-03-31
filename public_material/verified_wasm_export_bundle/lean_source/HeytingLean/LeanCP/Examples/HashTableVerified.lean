import HeytingLean.LeanCP.Lang.CSemanticsDecEq
import HeytingLean.LeanCP.VCG.SWPCallSound
import HeytingLean.LeanCP.Core.VarLemmas
import HeytingLean.LeanCP.Tactics.Forward

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

set_option linter.unnecessarySimpa false

def makeHashNodeBody : CStmt :=
  .seq (.alloc "node" 3)
    (.seq (.assign (.fieldAccess (.var "node") "data") (.var "key"))
      (.seq (.assign (.fieldAccess (.var "node") "next") (.var "head"))
        (.seq (.assign (.fieldAccess (.var "node") "prev") .null)
          (.ret (.var "node")))))

def hashInsertBody : CStmt :=
  .seq (.assign (.var "node")
      (.call "make_hash_node" [.var "key", .arrayAccess (.var "table") (.intLit 0)]))
    (.seq (.assign (.deref (.binop .add (.var "table") (.intLit 0))) (.var "node"))
      (.ret (.var "node")))

/-- Read-only state predicate for a single hash-node cell layout. -/
def hashNodeAt_s (base : Nat) (key : Int) (head prev : CVal) : SProp := fun st =>
  st.heap.read base = some (.int key) ∧
  st.heap.read (base + 1) = some head ∧
  st.heap.read (base + 2) = some prev

def makeHashNodeSpecAt (base : Nat) (key : Int) (head : CVal) : SFunSpec where
  name := "make_hash_node"
  params := [("key", .int), ("head", .ptr (.struct "dll"))]
  retType := .ptr (.struct "dll")
  pre := fun st =>
    st.lookupVar "key" = some (.int key) ∧
    st.lookupVar "head" = some head ∧
    st.nextAddr = base ∧
    st.mem.nextBlock ≠ 0
  post := fun _ _ => True
  body := makeHashNodeBody

def hashFunEnvAt (base : Nat) (key : Int) (head : CVal) : FunEnv
  | "make_hash_node" => some (makeHashNodeSpecAt base key head)
  | _ => none

def hashCallPtr (st : CState) : PtrVal :=
  { block := st.mem.nextBlock, offset := 0 }

def hashCallAlloc (st : CState) (base : Nat) : FlatAlloc :=
  { base := base, block := st.mem.nextBlock, cells := 3 }

def hashCalleeEntryState (st : CState) (base : Nat) (key : Int) (head : CVal) : CState :=
  { (callEntryState st (makeHashNodeSpecAt base key head) [.int key, head]) with
      nextAddr := base }

def hashCalleeAllocState (st : CState) (base : Nat) (key : Int) (head : CVal) : CState :=
  (hashCalleeEntryState st base key head).allocCells "node" 3

def hashCalleeKeyState (st : CState) (base : Nat) (key : Int) (head : CVal) : CState :=
  let st1 := hashCalleeAllocState st base key head
  st1.withHeap (st1.heap.write base (.int key))

def hashCalleeNextState (st : CState) (base : Nat) (key : Int) (head : CVal) : CState :=
  let st2 := hashCalleeKeyState st base key head
  st2.withHeap (st2.heap.write (base + 1) head)

def hashCalleeFinalState (st : CState) (base : Nat) (key : Int) (head : CVal) : CState :=
  let st3 := hashCalleeNextState st base key head
  st3.withHeap (st3.heap.write (base + 2) .null)

def hashCallState (st : CState) (base : Nat) (key : Int) (head : CVal) : CState :=
  restoreCallerState st (hashCalleeFinalState st base key head)

def hashInsertFinalState (st : CState) (tableBase : Nat) (base : Nat) (key : Int) (head : CVal) : CState :=
  let node := CVal.ptrAddr (hashCallPtr st)
  let st1 := (hashCallState st base key head).updateVar "node" node
  st1.withHeap (st1.heap.write tableBase node)

theorem makeHashNode_execCall_exact (tableBase : Nat) (base : Nat) (key : Int) (head : CVal) :
    ∀ st,
      st.lookupVar "table" = some (.ptr 0 (Int.ofNat tableBase)) →
      st.lookupVar "key" = some (.int key) →
      st.heap.read tableBase = some head →
      st.nextAddr = base →
      st.mem.nextBlock ≠ 0 →
      execCall (hashFunEnvAt base key head) 10 "make_hash_node"
        [.var "key", .arrayAccess (.var "table") (.intLit 0)] st =
        some (CVal.ptrAddr (hashCallPtr st), hashCallState st base key head) := by
  intro st htable hkey hhead hbase hblock
  let entry : CState := callEntryState st (makeHashNodeSpecAt base key head) [.int key, head]
  let block := st.mem.nextBlock
  let ptr : PtrVal := { block := block, offset := 0 }
  let st1 := entry.allocCells "node" 3
  let st2 := st1.withHeap (st1.heap.write base (.int key))
  let st3 := st2.withHeap (st2.heap.write (base + 1) head)
  let st4 := st3.withHeap (st3.heap.write (base + 2) .null)
  have hallocfresh3 :
      (st.mem.alloc 0 3 .Freeable).1 = block := by
    simpa [block] using
      (Mem.alloc_fresh st.mem 0 3 .Freeable
        ((st.mem.alloc 0 3 .Freeable).1)
        ((st.mem.alloc 0 3 .Freeable).2) rfl)
  have hbind :
      bindCallEnv (makeHashNodeSpecAt base key head).params [.int key, head] =
        [("key", .int key), ("head", head)] := by
    rfl
  have hEvalHead :
      evalExpr (.arrayAccess (.var "table") (.intLit 0)) st = some head := by
    have hReadHead :
        st.readPtr { block := 0, offset := Int.ofNat tableBase } = some head := by
      simpa [hhead] using (CState.readPtr_block0 st tableBase tableBase)
    simpa [evalExpr, evalStaticExpr, htable] using hReadHead
  have hentryKey : entry.lookupVar "key" = some (.int key) := by
    simp [entry, callEntryState, hbind, CState.lookupVar]
  have hentryHead : entry.lookupVar "head" = some head := by
    simp [entry, callEntryState, hbind, CState.lookupVar, List.lookup]
  have hnode1 : st1.lookupVar "node" = some (CVal.ptrAddr ptr) := by
    simp [st1, entry, ptr, block, CVal.ptrAddr, CState.lookupVar, CState.allocCells, hallocfresh3]
  have hnode2 : st2.lookupVar "node" = some (CVal.ptrAddr ptr) := by
    simpa [st2, CState.lookupVar, CState.withHeap] using hnode1
  have hnode3 : st3.lookupVar "node" = some (CVal.ptrAddr ptr) := by
    simpa [st3, CState.lookupVar, CState.withHeap] using hnode2
  have hnode4 : st4.lookupVar "node" = some (CVal.ptrAddr ptr) := by
    simpa [st4, CState.lookupVar, CState.withHeap] using hnode3
  have hkey1 : st1.lookupVar "key" = some (.int key) := by
    simpa [st1, CState.lookupVar, CState.allocCells] using hentryKey
  have hhead2 : st2.lookupVar "head" = some head := by
    simpa [st2, CState.lookupVar, CState.withHeap] using hentryHead
  have hEvalKey1 : evalExpr (.var "key") st1 = some (.int key) := by
    simpa [evalExpr] using hkey1
  have hEvalHead2 : evalExpr (.var "head") st2 = some head := by
    simpa [evalExpr] using hhead2
  have hEvalNode4 : evalExpr (.var "node") st4 = some (CVal.ptrAddr ptr) := by
    simpa [evalExpr] using hnode4
  have hfind1 : st1.findAllocByBlock block = some { base := base, block := block, cells := 3 } := by
    simp [st1, entry, CState.findAllocByBlock, CState.allocCells, hbase, block, hallocfresh3]
  have hresolveData : st1.resolvePtr ptr = some base := by
    simpa [ptr, block, hbase] using
      (CState.resolvePtr_tracked st1 { base := base, block := block, cells := 3 } 0 hfind1 hblock (by decide : 0 < 3))
  have hwriteData : st1.writePtr ptr (.int key) = some st2 := by
    rw [CState.writePtr, hresolveData]
    change some (st1.withHeap (st1.heap.write base (.int key))) = some st2
    rfl
  have hMapWriteData :
      Option.map ExecResult.normal (st1.writePtr ptr (.int key)) = some (.normal st2) := by
    rw [hwriteData]
    rfl
  have hfind2 : st2.findAllocByBlock block = some { base := base, block := block, cells := 3 } := by
    simp [st2, st1, entry, CState.findAllocByBlock, CState.allocCells, CState.withHeap, hbase, block, hallocfresh3]
  have hresolveNext :
      st2.resolvePtr { block := block, offset := 1 } = some (base + 1) := by
    simpa [block, hbase] using
      (CState.resolvePtr_tracked st2 { base := base, block := block, cells := 3 } 1 hfind2 hblock (by decide : 1 < 3))
  have hwriteNext : st2.writePtr { block := block, offset := 1 } head = some st3 := by
    rw [CState.writePtr, hresolveNext]
    change some (st2.withHeap (st2.heap.write (base + 1) head)) = some st3
    rfl
  have hMapWriteNext :
      Option.map ExecResult.normal (st2.writePtr { block := block, offset := 1 } head) = some (.normal st3) := by
    rw [hwriteNext]
    rfl
  have hfind3 : st3.findAllocByBlock block = some { base := base, block := block, cells := 3 } := by
    simp [st3, st2, st1, entry, CState.findAllocByBlock, CState.allocCells, CState.withHeap, hbase, block, hallocfresh3]
  have hresolvePrev :
      st3.resolvePtr { block := block, offset := 2 } = some (base + 2) := by
    simpa [block, hbase] using
      (CState.resolvePtr_tracked st3 { base := base, block := block, cells := 3 } 2 hfind3 hblock (by decide : 2 < 3))
  have hwritePrev : st3.writePtr { block := block, offset := 2 } .null = some st4 := by
    rw [CState.writePtr, hresolvePrev]
    change some (st3.withHeap (st3.heap.write (base + 2) .null)) = some st4
    rfl
  have hMapWritePrev :
      Option.map ExecResult.normal (st3.writePtr { block := block, offset := 2 } .null) = some (.normal st4) := by
    rw [hwritePrev]
    rfl
  have hExecAlloc :
      execStmt 9 (.alloc "node" 3) entry = some (.normal st1) := by
    simp [execStmt, st1]
  have hExecAssignData :
      execStmt 8 (.assign (.fieldAccess (.var "node") "data") (.var "key")) st1 =
        some (.normal st2) := by
    simp [execStmt, hEvalKey1, hnode1, CVal.ptrAddr]
    simpa [ptr, block, PtrVal.addOffset, Addr.addOffset, fieldOffset] using hMapWriteData
  have hExecAssignNext :
      execStmt 7 (.assign (.fieldAccess (.var "node") "next") (.var "head")) st2 =
        some (.normal st3) := by
    simp [execStmt, hEvalHead2, hnode2, CVal.ptrAddr]
    simpa [ptr, block, PtrVal.addOffset, Addr.addOffset, fieldOffset] using hMapWriteNext
  have hExecAssignPrev :
      execStmt 6 (.assign (.fieldAccess (.var "node") "prev") .null) st3 =
        some (.normal st4) := by
    simp [execStmt, hnode3, CVal.ptrAddr]
    simpa [evalExpr, evalStaticExpr, ptr, block, PtrVal.addOffset, Addr.addOffset, fieldOffset] using hMapWritePrev
  have hExecRetNode :
      execStmt 6 (.ret (.var "node")) st4 = some (.returned (CVal.ptrAddr ptr) st4) := by
    simp [execStmt, hEvalNode4]
  have hRetNodeRaw :
      (st4.lookupVar "node").bind (fun v => some (ExecResult.returned v st4)) =
        some (ExecResult.returned (CVal.ptrAddr ptr) st4) := by
    simpa [execStmt] using hExecRetNode
  have hAssignPrevRaw :
      ((evalExpr .null st3).bind fun v =>
          (st3.lookupVar "node").bind fun pv =>
            match pv with
            | .ptr block offset =>
                (PtrVal.addOffset { block := block, offset := offset } (Int.ofNat (fieldOffset "prev"))).bind
                  fun slot => Option.map ExecResult.normal (st3.writePtr slot v)
            | _ => none) =
        some (.normal st4) := by
    simpa [execStmt] using hExecAssignPrev
  have hExecTail :
      execStmt 7
          (.seq (.assign (.fieldAccess (.var "node") "prev") .null) (.ret (.var "node"))) st3 =
        some (.returned (CVal.ptrAddr ptr) st4) := by
    have hSeqRaw :
        (((evalExpr .null st3).bind fun v =>
            (st3.lookupVar "node").bind fun pv =>
              match pv with
              | .ptr block offset =>
                  (PtrVal.addOffset { block := block, offset := offset } (Int.ofNat (fieldOffset "prev"))).bind
                    fun slot => Option.map ExecResult.normal (st3.writePtr slot v)
              | _ => none).bind
          fun __do_lift =>
            match __do_lift with
            | ExecResult.normal st' => (st'.lookupVar "node").bind (fun v => some (ExecResult.returned v st'))
            | ExecResult.returned v st' => some (ExecResult.returned v st')) =
          some (ExecResult.returned (CVal.ptrAddr ptr) st4) := by
      rw [hAssignPrevRaw]
      exact hRetNodeRaw
    simpa [execStmt] using hSeqRaw
  have hAssignNextRaw :
      ((st2.lookupVar "head").bind fun v =>
          (st2.lookupVar "node").bind fun pv =>
            match pv with
            | .ptr block offset =>
                (PtrVal.addOffset { block := block, offset := offset } (Int.ofNat (fieldOffset "next"))).bind
                  fun slot => Option.map ExecResult.normal (st2.writePtr slot v)
            | _ => none) =
        some (.normal st3) := by
    simpa [execStmt] using hExecAssignNext
  have hExecAfterNext :
      execStmt 8
          (.seq (.assign (.fieldAccess (.var "node") "next") (.var "head"))
            (.seq (.assign (.fieldAccess (.var "node") "prev") .null) (.ret (.var "node"))))
          st2 =
        some (.returned (CVal.ptrAddr ptr) st4) := by
    have hSeqRaw :
        (((st2.lookupVar "head").bind fun v =>
            (st2.lookupVar "node").bind fun pv =>
              match pv with
              | .ptr block offset =>
                  (PtrVal.addOffset { block := block, offset := offset } (Int.ofNat (fieldOffset "next"))).bind
                    fun slot => Option.map ExecResult.normal (st2.writePtr slot v)
              | _ => none).bind
          fun __do_lift =>
            match __do_lift with
            | ExecResult.normal st' =>
                execStmt 7 (.seq (.assign (.fieldAccess (.var "node") "prev") .null) (.ret (.var "node"))) st'
            | ExecResult.returned v st' => some (ExecResult.returned v st')) =
          some (ExecResult.returned (CVal.ptrAddr ptr) st4) := by
      rw [hAssignNextRaw]
      exact hExecTail
    simpa [execStmt] using hSeqRaw
  have hAssignDataRaw :
      ((st1.lookupVar "key").bind fun v =>
          (st1.lookupVar "node").bind fun pv =>
            match pv with
            | .ptr block offset =>
                (PtrVal.addOffset { block := block, offset := offset } (Int.ofNat (fieldOffset "data"))).bind
                  fun slot => Option.map ExecResult.normal (st1.writePtr slot v)
            | _ => none) =
        some (.normal st2) := by
    simpa [execStmt] using hExecAssignData
  have hExecAfterAlloc :
      execStmt 9
          (.seq (.assign (.fieldAccess (.var "node") "data") (.var "key"))
            (.seq (.assign (.fieldAccess (.var "node") "next") (.var "head"))
              (.seq (.assign (.fieldAccess (.var "node") "prev") .null) (.ret (.var "node")))))
          st1 =
        some (.returned (CVal.ptrAddr ptr) st4) := by
    have hSeqRaw :
        (((st1.lookupVar "key").bind fun v =>
            (st1.lookupVar "node").bind fun pv =>
              match pv with
              | .ptr block offset =>
                  (PtrVal.addOffset { block := block, offset := offset } (Int.ofNat (fieldOffset "data"))).bind
                    fun slot => Option.map ExecResult.normal (st1.writePtr slot v)
              | _ => none).bind
          fun __do_lift =>
            match __do_lift with
            | ExecResult.normal st' =>
                execStmt 8
                  (.seq (.assign (.fieldAccess (.var "node") "next") (.var "head"))
                    (.seq (.assign (.fieldAccess (.var "node") "prev") .null) (.ret (.var "node"))))
                  st'
            | ExecResult.returned v st' => some (ExecResult.returned v st')) =
          some (ExecResult.returned (CVal.ptrAddr ptr) st4) := by
      rw [hAssignDataRaw]
      exact hExecAfterNext
    simpa [execStmt] using hSeqRaw
  have hExecBody :
      execStmt 10 makeHashNodeBody entry = some (.returned (CVal.ptrAddr ptr) st4) := by
    have hSeqRaw :
        (match execStmt 9 (.alloc "node" 3) entry with
        | some (.normal st') =>
            execStmt 9
              (.seq (.assign (.fieldAccess (.var "node") "data") (.var "key"))
                (.seq (.assign (.fieldAccess (.var "node") "next") (.var "head"))
                  (.seq (.assign (.fieldAccess (.var "node") "prev") .null) (.ret (.var "node")))))
              st'
        | some (.returned v st') => some (.returned v st')
        | none => none) =
          some (.returned (CVal.ptrAddr ptr) st4) := by
      rw [hExecAlloc]
      exact hExecAfterAlloc
    simpa [makeHashNodeBody, execStmt] using hSeqRaw
  have hRestore :
      restoreCallerState st st4 = hashCallState st base key head := by
    cases st with
    | mk heap env nextAddr mem allocs =>
        simp at hbase
        cases hbase
        rfl
  have hCallBind :=
      congrArg
        (fun res =>
          Option.bind res (fun a =>
            match a with
            | .returned ret callee => some (ret, restoreCallerState st callee)
            | .normal callee => some (.undef, restoreCallerState st callee)))
        hExecBody
  simpa [execCall, hashFunEnvAt, evalArgs, htable, hkey, hEvalHead, hbase, makeHashNodeSpecAt,
    hRestore, hashCallPtr, block, ptr, CVal.ptrAddr] using hCallBind

theorem hashInsert_executes_from_state (tableBase : Nat) (base : Nat) (key : Int) (head : CVal) :
    ∀ st,
      st.lookupVar "table" = some (.ptr 0 (Int.ofNat tableBase)) →
      st.lookupVar "key" = some (.int key) →
      st.heap.read tableBase = some head →
      st.nextAddr = base →
      st.mem.nextBlock ≠ 0 →
      execStmtFull (hashFunEnvAt base key head) 12 hashInsertBody st =
        some (.returned (CVal.ptrAddr (hashCallPtr st)) (hashInsertFinalState st tableBase base key head)) := by
  intro st htable hkey hhead hbase hblock
  have hCall :=
    makeHashNode_execCall_exact tableBase base key head st htable hkey hhead hbase hblock
  let node := CVal.ptrAddr (hashCallPtr st)
  let stCall := hashCallState st base key head
  let st1 := stCall.updateVar "node" node
  let st2 := hashInsertFinalState st tableBase base key head
  have htable1 : st1.lookupVar "table" = some (.ptr 0 (Int.ofNat tableBase)) := by
    calc
      st1.lookupVar "table" = stCall.lookupVar "table" := by
        simpa [st1] using lookupVar_updateVar_ne stCall "node" "table" node (by decide : "table" ≠ "node")
      _ = some (.ptr 0 (Int.ofNat tableBase)) := by
        simpa [stCall, hashCallState, restoreCallerState, CState.lookupVar] using htable
  have hnode1 : st1.lookupVar "node" = some node := by
    simpa [st1] using lookupVar_updateVar_eq stCall "node" node
  have hEvalTable :
      evalExpr (.binop .add (.var "table") (.intLit 0)) st1 =
        some (CVal.ptr 0 (Int.ofNat tableBase)) := by
    simpa [evalExpr, evalStaticExpr, htable1] using
      (show evalBinOp .add (CVal.ptr 0 (Int.ofNat tableBase)) (.int 0) =
          some (CVal.ptr 0 (Int.ofNat tableBase)) by
        change (if 0 ≤ (0 : Int) then
            some (CVal.ptr 0 (Int.ofNat tableBase + 0))
          else none) = some (CVal.ptr 0 (Int.ofNat tableBase))
        simp)
  have hWriteTable :
      st1.writePtr { block := 0, offset := Int.ofNat tableBase } node = some st2 := by
    rw [CState.writePtr_block0 st1 tableBase tableBase node]
    change some (st1.withHeap (st1.heap.write tableBase node)) = some st2
    rfl
  have hMapWriteTable :
      Option.map ExecResult.normal (st1.writePtr { block := 0, offset := Int.ofNat tableBase } node) =
        some (.normal st2) := by
    rw [hWriteTable]
    rfl
  have hExecAssignTable :
      execStmtFull (hashFunEnvAt base key head) 10
        (.assign (.deref (.binop .add (.var "table") (.intLit 0))) (.var "node")) st1 =
        some (.normal st2) := by
    simp [execStmtFull, hnode1, hEvalTable]
    simpa using hMapWriteTable
  have hEvalRet : evalExpr (.var "node") st2 = some node := by
    simpa [evalExpr, st2, hashInsertFinalState, CState.lookupVar, CState.withHeap] using hnode1
  have hExecRet :
      execStmtFull (hashFunEnvAt base key head) 10 (.ret (.var "node")) st2 =
        some (.returned node st2) := by
    simp [execStmtFull, hEvalRet]
  have hExecTail :
      execStmtFull (hashFunEnvAt base key head) 11
        (.seq (.assign (.deref (.binop .add (.var "table") (.intLit 0))) (.var "node"))
          (.ret (.var "node"))) st1 =
        some (.returned node st2) := by
    have hAssignTableRaw :
        ((st1.lookupVar "node").bind fun v =>
            (evalExpr (.binop .add (.var "table") (.intLit 0)) st1).bind fun pv =>
              match pv with
              | .ptr block offset =>
                  Option.map ExecResult.normal (st1.writePtr { block := block, offset := offset } v)
              | _ => none) =
          some (.normal st2) := by
      simpa [execStmtFull] using hExecAssignTable
    have hRetRaw :
        (st2.lookupVar "node").bind (fun v => some (ExecResult.returned v st2)) =
          some (.returned node st2) := by
      simpa [execStmtFull] using hExecRet
    have hSeqRaw :
        (((st1.lookupVar "node").bind fun v =>
            (evalExpr (.binop .add (.var "table") (.intLit 0)) st1).bind fun pv =>
              match pv with
              | .ptr block offset =>
                  Option.map ExecResult.normal (st1.writePtr { block := block, offset := offset } v)
              | _ => none).bind
          fun __do_lift =>
            match __do_lift with
            | ExecResult.normal st' => (st'.lookupVar "node").bind (fun v => some (ExecResult.returned v st'))
            | ExecResult.returned v st' => some (ExecResult.returned v st')) =
          some (ExecResult.returned node st2) := by
      rw [hAssignTableRaw]
      exact hRetRaw
    simpa [execStmtFull] using hSeqRaw
  have hCallAssign :
      execStmtFull (hashFunEnvAt base key head) 11
        (.assign (.var "node")
          (.call "make_hash_node" [.var "key", .arrayAccess (.var "table") (.intLit 0)])) st =
        some (.normal st1) := by
    simp [execStmtFull, hCall, st1, stCall, node]
  have hCallAssignRaw :
      ((execCall (hashFunEnvAt base key head) 10 "make_hash_node"
            [.var "key", .arrayAccess (.var "table") (.intLit 0)] st).bind
          fun __discr => some (ExecResult.normal (__discr.2.updateVar "node" __discr.1))) =
        some (.normal st1) := by
    simpa [execStmtFull] using hCallAssign
  have hExecBody :
      execStmtFull (hashFunEnvAt base key head) 12 hashInsertBody st =
        some (.returned node st2) := by
    have hSeqRaw :
        (((execCall (hashFunEnvAt base key head) 10 "make_hash_node"
              [.var "key", .arrayAccess (.var "table") (.intLit 0)] st).bind
            fun __discr => some (ExecResult.normal (__discr.2.updateVar "node" __discr.1))).bind
          fun __do_lift =>
            match __do_lift with
            | ExecResult.normal st' =>
                execStmtFull (hashFunEnvAt base key head) 11
                  (.seq (.assign (.deref (.binop .add (.var "table") (.intLit 0))) (.var "node"))
                    (.ret (.var "node"))) st'
            | ExecResult.returned v st' => some (ExecResult.returned v st')) =
          some (ExecResult.returned node st2) := by
      rw [hCallAssignRaw]
      exact hExecTail
    simpa [hashInsertBody, execStmtFull] using hSeqRaw
  simpa [node, st2, hashInsertFinalState] using hExecBody

theorem hashInsert_correct (tableBase : Nat) (base : Nat) (key : Int) (head : CVal) :
    ∀ st,
      st.lookupVar "table" = some (.ptr 0 (Int.ofNat tableBase)) →
      st.lookupVar "key" = some (.int key) →
      st.heap.read tableBase = some head →
      st.nextAddr = base →
      st.mem.nextBlock ≠ 0 →
      tableBase ≠ base →
      tableBase ≠ base + 1 →
      tableBase ≠ base + 2 →
      ∃ st',
        execStmtFull (hashFunEnvAt base key head) 12 hashInsertBody st =
          some (.returned (CVal.ptrAddr (hashCallPtr st)) st') ∧
        st'.lookupVar "table" = some (.ptr 0 (Int.ofNat tableBase)) ∧
        st'.lookupVar "key" = some (.int key) ∧
        st'.lookupVar "node" = some (CVal.ptrAddr (hashCallPtr st)) ∧
        st'.heap.read tableBase = some (CVal.ptrAddr (hashCallPtr st)) ∧
        hashNodeAt_s base key head .null st' := by
  intro st htable hkey hhead hbase hblock hfresh0 hfresh1 hfresh2
  refine ⟨hashInsertFinalState st tableBase base key head, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hashInsert_executes_from_state tableBase base key head st htable hkey hhead hbase hblock
  · calc
      (hashInsertFinalState st tableBase base key head).lookupVar "table" =
          ((hashCallState st base key head).updateVar "node" (CVal.ptrAddr (hashCallPtr st))).lookupVar "table" := by
            simp [hashInsertFinalState, CState.lookupVar, CState.withHeap]
      _ = (hashCallState st base key head).lookupVar "table" := by
        simpa using lookupVar_updateVar_ne (hashCallState st base key head) "node" "table"
          (CVal.ptrAddr (hashCallPtr st)) (by decide : "table" ≠ "node")
      _ = some (.ptr 0 (Int.ofNat tableBase)) := by
        simpa [hashCallState, restoreCallerState, CState.lookupVar] using htable
  · calc
      (hashInsertFinalState st tableBase base key head).lookupVar "key" =
          ((hashCallState st base key head).updateVar "node" (CVal.ptrAddr (hashCallPtr st))).lookupVar "key" := by
            simp [hashInsertFinalState, CState.lookupVar, CState.withHeap]
      _ = (hashCallState st base key head).lookupVar "key" := by
        simpa using lookupVar_updateVar_ne (hashCallState st base key head) "node" "key"
          (CVal.ptrAddr (hashCallPtr st)) (by decide : "key" ≠ "node")
      _ = some (.int key) := by
        simpa [hashCallState, restoreCallerState, CState.lookupVar] using hkey
  · simpa [hashInsertFinalState, CState.lookupVar, CState.withHeap] using
      (lookupVar_updateVar_eq (hashCallState st base key head) "node" (CVal.ptrAddr (hashCallPtr st)))
  · simp [hashInsertFinalState, CState.withHeap, Heap.read, Heap.write]
  · constructor
    · have hbaseRead :
          (hashCallState st base key head).heap.read base = some (.int key) := by
        simp [hashCallState, hashCalleeFinalState, hashCalleeNextState, hashCalleeKeyState,
          hashCalleeAllocState, hashCalleeEntryState, CState.withHeap, CState.allocCells,
          Heap.read, Heap.write]
      calc
        (hashInsertFinalState st tableBase base key head).heap.read base =
            (((hashCallState st base key head).updateVar "node" (CVal.ptrAddr (hashCallPtr st))).heap.write tableBase
              (CVal.ptrAddr (hashCallPtr st))).read base := by
                rfl
        _ = (hashCallState st base key head).heap.read base := by
              simp [CState.updateVar, Heap.read, Heap.write]
              have hne' : base ≠ tableBase := by
                intro hEq
                exact hfresh0 hEq.symm
              rw [Finmap.lookup_insert_of_ne (hashCallState st base key head).heap hne']
        _ = some (.int key) := hbaseRead
    · constructor
      · have hnextRead :
            (hashCallState st base key head).heap.read (base + 1) = some head := by
          simp [hashCallState, hashCalleeFinalState, hashCalleeNextState, hashCalleeKeyState,
            hashCalleeAllocState, hashCalleeEntryState, CState.withHeap, CState.allocCells,
            Heap.read, Heap.write]
        calc
          (hashInsertFinalState st tableBase base key head).heap.read (base + 1) =
              (((hashCallState st base key head).updateVar "node" (CVal.ptrAddr (hashCallPtr st))).heap.write tableBase
                (CVal.ptrAddr (hashCallPtr st))).read (base + 1) := by
                  rfl
          _ = (hashCallState st base key head).heap.read (base + 1) := by
                simp [CState.updateVar, Heap.read, Heap.write]
                have hne' : base + 1 ≠ tableBase := by
                  intro hEq
                  exact hfresh1 hEq.symm
                rw [Finmap.lookup_insert_of_ne (hashCallState st base key head).heap hne']
          _ = some head := hnextRead
      · have hprevRead :
            (hashCallState st base key head).heap.read (base + 2) = some .null := by
          simp [hashCallState, hashCalleeFinalState, hashCalleeNextState, hashCalleeKeyState,
            hashCalleeAllocState, hashCalleeEntryState, CState.withHeap, CState.allocCells,
            Heap.read, Heap.write]
        calc
          (hashInsertFinalState st tableBase base key head).heap.read (base + 2) =
              (((hashCallState st base key head).updateVar "node" (CVal.ptrAddr (hashCallPtr st))).heap.write tableBase
                (CVal.ptrAddr (hashCallPtr st))).read (base + 2) := by
                  rfl
          _ = (hashCallState st base key head).heap.read (base + 2) := by
                simp [CState.updateVar, Heap.read, Heap.write]
                have hne' : base + 2 ≠ tableBase := by
                  intro hEq
                  exact hfresh2 hEq.symm
                rw [Finmap.lookup_insert_of_ne (hashCallState st base key head).heap hne']
          _ = some .null := hprevRead

def makeHashNodeSpec : SFunSpec where
  name := "make_hash_node"
  params := [("key", .int), ("head", .ptr (.struct "dll"))]
  retType := .ptr (.struct "dll")
  pre := fun _ => True
  post := fun ret st =>
    ∃ key head ptr,
      st.lookupVar "key" = some (.int key) ∧
      st.lookupVar "head" = some head ∧
      ret = CVal.ptrAddr ptr ∧
      st.heap.read 400 = some (.int key) ∧
      st.heap.read 401 = some head ∧
      st.heap.read 402 = some .null
  body := makeHashNodeBody

def hashFunEnv : FunEnv
  | "make_hash_node" => some makeHashNodeSpec
  | _ => none

def hashInsertInit : CState :=
  { heap := Heap.empty.write 300 .null
    env := [("table", .ptr 0 300), ("key", .int 7)]
    nextAddr := 400 }

def hashNodeBlock : Block :=
  ((heapToMem (Heap.empty.write 300 .null)).alloc 0 (Int.ofNat 3) .Freeable).1

def hashNodePtr : PtrVal := { block := hashNodeBlock, offset := 0 }

def hashInsertAlloc : FlatAlloc := { base := 400, block := hashNodeBlock, cells := 3 }

def hashInsertFinal : CState :=
  let heap :=
    ((((Heap.empty.write 300 .null).write 400 (.int 7)).write 401 .null).write 402 .null).write 300
      (CVal.ptrAddr hashNodePtr)
  { heap := heap
    env := [("node", CVal.ptrAddr hashNodePtr), ("table", .ptr 0 300), ("key", .int 7)]
    nextAddr := 403
    mem := CState.syncMem heap [hashInsertAlloc]
      (((heapToMem (Heap.empty.write 300 .null)).alloc 0 (Int.ofNat 3) .Freeable).2.nextBlock)
    allocs := [hashInsertAlloc] }

theorem hashTable_executes :
    execStmtFull hashFunEnv 12 hashInsertBody hashInsertInit =
      some (.returned (CVal.ptrAddr hashNodePtr) hashInsertFinal) := by
  native_decide

theorem hashTable_verified :
    ∃ st',
      execStmtFull hashFunEnv 12 hashInsertBody hashInsertInit =
        some (.returned (CVal.ptrAddr hashNodePtr) st') ∧
      st'.heap.read 300 = some (CVal.ptrAddr hashNodePtr) ∧
      st'.heap.read 400 = some (.int 7) ∧
      st'.heap.read 401 = some .null ∧
      st'.heap.read 402 = some .null := by
  refine ⟨hashInsertFinal, hashTable_executes, ?_, ?_, ?_, ?_⟩ <;>
    simp [hashInsertFinal]

theorem hashTable_forward_verified :
    swpFull hashFunEnv
      (.assign (.var "node")
        (.call "make_hash_node" [.var "key", .arrayAccess (.var "table") (.intLit 0)]))
      (fun _ st =>
        st.lookupVar "table" = some (.ptr 0 300) ∧
        st.lookupVar "key" = some (.int 7) ∧
        ∃ key head ptr,
          st.lookupVar "node" = some (CVal.ptrAddr ptr) ∧
          st.heap.read 400 = some (.int key) ∧
          st.heap.read 401 = some head ∧
          st.heap.read 402 = some .null)
      hashInsertInit := by
  xstep
  refine ⟨makeHashNodeSpec, [.int 7, .null], ?_, ?_, ?_, ?_, ?_⟩
  · simp [hashFunEnv]
  · native_decide
  · simp [makeHashNodeSpec]
  · simp [makeHashNodeSpec]
  · intro ret callee hpost
    rcases hpost with ⟨key, head, ptr, hkey, hhead, hret, hdata, hnext, hprev⟩
    subst hret
    refine ⟨?_, ?_, ⟨key, head, ptr, ?_, ?_, ?_, ?_⟩⟩
    · simp [hashInsertInit, CState.lookupVar, CState.updateVar, List.lookup]
    · simp [hashInsertInit, CState.lookupVar, CState.updateVar, List.lookup]
    · simp [CState.lookupVar, CState.updateVar]
    · simpa [restoreCallerState, CState.updateVar] using hdata
    · simpa [restoreCallerState, CState.updateVar] using hnext
    · simpa [restoreCallerState, CState.updateVar] using hprev

end HeytingLean.LeanCP.Examples
