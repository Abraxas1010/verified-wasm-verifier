import HeytingLean.LeanCP.Lang.CSemanticsDecEq
import HeytingLean.LeanCP.Core.VarLemmas
import HeytingLean.LeanCP.Predicates.SLL
import HeytingLean.LeanCP.VCG.SWPCallSound
import HeytingLean.LeanCP.Tactics.Forward

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

set_option linter.unnecessarySimpa false

def makeStackNodeBody : CStmt :=
  .seq (.alloc "node" 2)
    (.seq (.assign (.fieldAccess (.var "node") "data") (.var "value"))
      (.seq (.assign (.fieldAccess (.var "node") "next") (.var "head"))
        (.ret (.var "node"))))

def stackPushPopBody : CStmt :=
  .seq (.assign (.var "node") (.call "make_stack_node" [.var "value", .var "head"]))
    (.seq (.assign (.var "head") (.var "node"))
      (.seq (.assign (.var "result") (.fieldAccess (.var "head") "data"))
        (.seq (.assign (.var "head") (.fieldAccess (.var "head") "next"))
          (.ret (.var "result")))))

def makeStackNodeSpecAt (base : Nat) (value : Int) (head : CVal) : SFunSpec where
  name := "make_stack_node"
  params := [("value", .int), ("head", .ptr (.struct "list"))]
  retType := .ptr (.struct "list")
  pre := fun st =>
    st.lookupVar "value" = some (.int value) ∧
    st.lookupVar "head" = some head ∧
    st.nextAddr = base ∧
    st.mem.nextBlock ≠ 0
  post := fun ret st =>
    ret = CVal.ptrAddr { block := base, offset := 0 } ∨
    ∃ ptr,
      ret = CVal.ptrAddr ptr ∧
      st.lookupVar "value" = some (.int value) ∧
      st.lookupVar "head" = some head ∧
      st.nextAddr = base + 2 ∧
      st.heap.read base = some (.int value) ∧
      st.heap.read (base + 1) = some head ∧
      st.readPtr ptr = some (.int value) ∧
      st.readPtr { block := ptr.block, offset := ptr.offset + 1 } = some head
  body := makeStackNodeBody

def makeStackNodeSpec : SFunSpec :=
  makeStackNodeSpecAt 500 5 .null

def stackFunEnvAt (base : Nat) (value : Int) (head : CVal) : FunEnv
  | "make_stack_node" => some (makeStackNodeSpecAt base value head)
  | _ => none

def stackFunEnv : FunEnv :=
  stackFunEnvAt 500 5 .null

def stackInitOf (value : Int) : CState :=
  { heap := Heap.empty
    env := [("head", .null), ("value", .int value)]
    nextAddr := 500 }

def stackInit : CState :=
  stackInitOf 5

def stackBlock : Block :=
  ((heapToMem Heap.empty).alloc 0 (Int.ofNat 2) .Freeable).1

def stackNodePtr : PtrVal := { block := stackBlock, offset := 0 }

def stackAlloc : FlatAlloc := { base := 500, block := stackBlock, cells := 2 }

def stackFinalOf (value : Int) : CState :=
  let heap := (Heap.empty.write 500 (.int value)).write 501 .null
  { heap := heap
    env := [("head", .null), ("result", .int value), ("node", CVal.ptrAddr stackNodePtr), ("value", .int value)]
    nextAddr := 502
    mem := CState.syncMem heap [stackAlloc] (((heapToMem Heap.empty).alloc 0 (Int.ofNat 2) .Freeable).2.nextBlock)
    allocs := [stackAlloc] }

def stackFinal : CState :=
  stackFinalOf 5

def stackCallPtr (st : CState) : PtrVal :=
  { block := st.mem.nextBlock, offset := 0 }

def stackCallAlloc (st : CState) (base : Nat) : FlatAlloc :=
  { base := base, block := st.mem.nextBlock, cells := 2 }

def stackCallHeap (st : CState) (base : Nat) (value : Int) (head : CVal) : Heap :=
  (st.heap.write base (.int value)).write (base + 1) head

def stackCalleeEntryState (st : CState) (base : Nat) (value : Int) (head : CVal) : CState :=
  { (callEntryState st (makeStackNodeSpecAt base value head) [.int value, head]) with
      nextAddr := base }

def stackCalleeAllocState (st : CState) (base : Nat) (value : Int) (head : CVal) : CState :=
  (stackCalleeEntryState st base value head).allocCells "node" 2

def stackCalleeDataState (st : CState) (base : Nat) (value : Int) (head : CVal) : CState :=
  let st1 := stackCalleeAllocState st base value head
  st1.withHeap (st1.heap.write base (.int value))

def stackCalleeFinalState (st : CState) (base : Nat) (value : Int) (head : CVal) : CState :=
  let st2 := stackCalleeDataState st base value head
  st2.withHeap (st2.heap.write (base + 1) head)

def stackCallState (st : CState) (base : Nat) (value : Int) (head : CVal) : CState :=
  restoreCallerState st (stackCalleeFinalState st base value head)

def stackPushPopFinalState (st : CState) (base : Nat) (value : Int) (head : CVal) : CState :=
  let node := CVal.ptrAddr (stackCallPtr st)
  let st1 := (stackCallState st base value head).updateVar "node" node
  let st2 := st1.updateVar "head" node
  let st3 := st2.updateVar "result" (.int value)
  st3.updateVar "head" head

private theorem resolvePtr_updateVar (st : CState) (x : String) (v : CVal) (ptr : PtrVal) :
    (st.updateVar x v).resolvePtr ptr = st.resolvePtr ptr := by
  cases st
  rfl

private theorem readPtr_updateVar (st : CState) (x : String) (v : CVal) (ptr : PtrVal) :
    (st.updateVar x v).readPtr ptr = st.readPtr ptr := by
  cases st
  rfl

private theorem writeBlock_two_overwrite (heap : Heap) (base : Nat) (v0 v1 : CVal) :
    ((writeBlock heap base 2).write base v0).write (base + 1) v1 =
      (heap.write base v0).write (base + 1) v1 := by
  have hrange : List.range 2 = [0, 1] := by decide
  apply Finmap.ext_lookup
  intro addr
  by_cases hbase : addr = base
  · subst addr
    have hne : base + 1 ≠ base := Nat.succ_ne_self base
    simp [writeBlock, hrange, Heap.write, Finmap.lookup_insert_of_ne, hne]
  · by_cases hnext : addr = base + 1
    · subst addr
      have hne : base ≠ base + 1 := Nat.ne_of_lt (Nat.lt_succ_self base)
      simp [writeBlock, hrange, Heap.write, Finmap.lookup_insert_of_ne, hne]
    · simp [writeBlock, hrange, Heap.write, Finmap.lookup_insert_of_ne, hbase, hnext]

private theorem writeBlock_two_data (heap : Heap) (base : Nat) (v0 : CVal) :
    (writeBlock heap base 2).write base v0 =
      (heap.write base v0).write (base + 1) .undef := by
  have hrange : List.range 2 = [0, 1] := by decide
  apply Finmap.ext_lookup
  intro addr
  by_cases hbase : addr = base
  · subst addr
    have hne : base + 1 ≠ base := Nat.succ_ne_self base
    simp [writeBlock, hrange, Heap.write, Finmap.lookup_insert_of_ne, hne]
  · by_cases hnext : addr = base + 1
    · subst addr
      have hne : base ≠ base + 1 := Nat.ne_of_lt (Nat.lt_succ_self base)
      simp [writeBlock, hrange, Heap.write, Finmap.lookup_insert_of_ne, hne]
    · simp [writeBlock, hrange, Heap.write, Finmap.lookup_insert_of_ne, hbase, hnext]

private theorem heapToMem_nextBlock (heap : Heap) :
    (heapToMem heap).nextBlock = 1 := by
  by_cases h : heap = ∅
  · simp [heapToMem, Heap.toMem, h]
  · simp [heapToMem, Heap.toMem, h]

private theorem stackCalleeDataState_allocs (st : CState) (base : Nat) (value : Int) (head : CVal) :
    (stackCalleeDataState st base value head).allocs = stackCallAlloc st base :: st.allocs := by
  cases st
  rfl

private theorem stackCalleeFinalState_allocs (st : CState) (base : Nat) (value : Int) (head : CVal) :
    (stackCalleeFinalState st base value head).allocs = stackCallAlloc st base :: st.allocs := by
  simp [stackCalleeFinalState, stackCalleeDataState_allocs]

private theorem stackCalleeDataState_heap (st : CState) (base : Nat) (value : Int) (head : CVal) :
    (stackCalleeDataState st base value head).heap =
      ((st.heap.write base (.int value)).write (base + 1) .undef) := by
  cases st with
  | mk heap env nextAddr mem allocs =>
      simpa [stackCalleeDataState, stackCalleeAllocState, stackCalleeEntryState, CState.allocCells, CState.withHeap] using
        (writeBlock_two_data heap base (.int value))

private theorem stackCalleeFinalState_heap (st : CState) (base : Nat) (value : Int) (head : CVal) :
    (stackCalleeFinalState st base value head).heap = stackCallHeap st base value head := by
  cases st with
  | mk heap env nextAddr mem allocs =>
      simpa [stackCalleeFinalState, stackCalleeDataState, stackCalleeAllocState, stackCalleeEntryState,
        CState.allocCells, CState.withHeap, stackCallHeap] using
        (writeBlock_two_overwrite heap base (.int value) head)

private theorem sll_s_addrs_same_heap
    (ptr : CVal) (xs : List Int) (heap : Heap)
    (env₁ env₂ : Env) (next₁ next₂ : Nat) (mem₁ mem₂ : Mem)
    (allocs₁ allocs₂ : List FlatAlloc) :
    sll_s_addrs ptr xs { heap := heap, env := env₁, nextAddr := next₁, mem := mem₁, allocs := allocs₁ } =
      sll_s_addrs ptr xs { heap := heap, env := env₂, nextAddr := next₂, mem := mem₂, allocs := allocs₂ } := by
  induction xs generalizing ptr with
  | nil =>
      cases ptr <;> simp [sll_s_addrs, ptrBase?]
  | cons x xs ih =>
      cases hbase : ptrBase? ptr with
      | none =>
          simp [sll_s_addrs, hbase]
      | some addr =>
          cases hnext : heap.read (Nat.succ addr + 1) with
          | none =>
              simp [sll_s_addrs, hbase, hnext]
          | some next =>
              simpa [sll_s_addrs, hbase, hnext] using congrArg (fun s => insert (Nat.succ addr) (insert (Nat.succ addr + 1) s)) (ih next)

private theorem ptr_eq_of_ptrBase_some {v : CVal} {addr : Nat}
    (hvPtr : ptrBase? v = some addr) :
    v = .ptr 0 (Int.ofNat (Nat.succ addr)) := by
  cases v with
  | null =>
      simp [ptrBase?] at hvPtr
  | int n =>
      simp [ptrBase?] at hvPtr
  | uint n sz =>
      simp [ptrBase?] at hvPtr
  | undef =>
      simp [ptrBase?] at hvPtr
  | structVal fields =>
      simp [ptrBase?] at hvPtr
  | unionVal tag val =>
      simp [ptrBase?] at hvPtr
  | float v =>
      simp [ptrBase?] at hvPtr
  | ptr block offset =>
      by_cases hblock : block = 0
      · subst hblock
        by_cases hnonneg : 0 ≤ offset
        · cases hnat : Int.toNat offset with
          | zero =>
              simp [ptrBase?, hnonneg, hnat] at hvPtr
          | succ addr' =>
              simp [ptrBase?, hnonneg, hnat] at hvPtr
              cases hvPtr
              have hoff : offset = Int.ofNat (Nat.succ addr) := by
                calc
                  offset = Int.ofNat (Int.toNat offset) := (Int.toNat_of_nonneg hnonneg).symm
                  _ = Int.ofNat (Nat.succ addr) := by simpa [hnat]
              simp [hoff]
        · simp [ptrBase?, hnonneg] at hvPtr
      · simp [ptrBase?, hblock] at hvPtr

private theorem sll_s_nonempty_eq_false_of_ptrBase_none
    {ptr : CVal} {h : Int} {t : List Int} {st : CState}
    (hbase : ptrBase? ptr = none) :
    sll_s ptr (h :: t) st = False := by
  cases ptr with
  | null =>
      simp [sll_s, ptrBase?]
  | int n =>
      simp [sll_s, ptrBase?] at hbase ⊢
  | uint n sz =>
      simp [sll_s, ptrBase?] at hbase ⊢
  | undef =>
      simp [sll_s, ptrBase?] at hbase ⊢
  | structVal fields =>
      simp [sll_s, ptrBase?] at hbase ⊢
  | unionVal tag val =>
      simp [sll_s, ptrBase?] at hbase ⊢
  | float v =>
      simp [sll_s, ptrBase?] at hbase ⊢
  | ptr block offset =>
      by_cases hblock : block = 0
      · subst hblock
        by_cases hnonneg : 0 ≤ offset
        · cases hnat : Int.toNat offset with
          | zero =>
              simp [sll_s, ptrBase?, hnonneg, hnat]
          | succ addr =>
              simp [ptrBase?, hnonneg, hnat] at hbase
        · simp [sll_s, ptrBase?, hnonneg]
      · simp [sll_s, ptrBase?, hblock]

private theorem sll_s_same_heap
    (ptr : CVal) (xs : List Int) (heap : Heap)
    (env₁ env₂ : Env) (next₁ next₂ : Nat) (mem₁ mem₂ : Mem)
    (allocs₁ allocs₂ : List FlatAlloc) :
    sll_s ptr xs { heap := heap, env := env₁, nextAddr := next₁, mem := mem₁, allocs := allocs₁ } ↔
      sll_s ptr xs { heap := heap, env := env₂, nextAddr := next₂, mem := mem₂, allocs := allocs₂ } := by
  induction xs generalizing ptr with
  | nil =>
      cases ptr with
      | null =>
          simp [sll_s, ptrBase?]
      | int n =>
          simp [sll_s, ptrBase?]
      | uint n sz =>
          simp [sll_s, ptrBase?]
      | undef =>
          simp [sll_s, ptrBase?]
      | structVal fields =>
          simp [sll_s, ptrBase?]
      | unionVal tag v =>
          simp [sll_s, ptrBase?]
      | float v =>
          simp [sll_s, ptrBase?]
      | ptr block offset =>
          by_cases hblock : block = 0
          · subst hblock
            by_cases hnonneg : 0 ≤ offset
            · cases hnat : Int.toNat offset <;> simp [sll_s, ptrBase?, hnonneg, hnat]
            · simp [sll_s, ptrBase?, hnonneg]
          · simp [sll_s, ptrBase?, hblock]
  | cons x xs ih =>
      cases hbase : ptrBase? ptr with
      | none =>
          constructor <;> intro hsll
          · rw [sll_s_nonempty_eq_false_of_ptrBase_none hbase] at hsll
            exact False.elim hsll
          · rw [sll_s_nonempty_eq_false_of_ptrBase_none hbase] at hsll
            exact False.elim hsll
      | some addr =>
          have hptr : ptr = .ptr 0 (Int.ofNat (Nat.succ addr)) := ptr_eq_of_ptrBase_some hbase
          subst ptr
          constructor <;> intro hsll
          · rcases (sll_s_cons_iff addr x xs
              { heap := heap, env := env₁, nextAddr := next₁, mem := mem₁, allocs := allocs₁ }).mp hsll with
                ⟨next, hdata, hnext, hrest, hnotData, hnotNext⟩
            have haddrs :
                sll_s_addrs next xs { heap := heap, env := env₁, nextAddr := next₁, mem := mem₁, allocs := allocs₁ } =
                  sll_s_addrs next xs { heap := heap, env := env₂, nextAddr := next₂, mem := mem₂, allocs := allocs₂ } :=
              sll_s_addrs_same_heap next xs heap env₁ env₂ next₁ next₂ mem₁ mem₂ allocs₁ allocs₂
            exact (sll_s_cons_iff addr x xs
              { heap := heap, env := env₂, nextAddr := next₂, mem := mem₂, allocs := allocs₂ }).mpr
                ⟨next, hdata, hnext, (ih next).mp hrest,
                  by simpa [haddrs] using hnotData,
                  by simpa [haddrs] using hnotNext⟩
          · rcases (sll_s_cons_iff addr x xs
              { heap := heap, env := env₂, nextAddr := next₂, mem := mem₂, allocs := allocs₂ }).mp hsll with
                ⟨next, hdata, hnext, hrest, hnotData, hnotNext⟩
            have haddrs :
                sll_s_addrs next xs { heap := heap, env := env₁, nextAddr := next₁, mem := mem₁, allocs := allocs₁ } =
                  sll_s_addrs next xs { heap := heap, env := env₂, nextAddr := next₂, mem := mem₂, allocs := allocs₂ } :=
              sll_s_addrs_same_heap next xs heap env₁ env₂ next₁ next₂ mem₁ mem₂ allocs₁ allocs₂
            exact (sll_s_cons_iff addr x xs
              { heap := heap, env := env₁, nextAddr := next₁, mem := mem₁, allocs := allocs₁ }).mpr
                ⟨next, hdata, hnext, (ih next).mpr hrest,
                  by simpa [haddrs] using hnotData,
                  by simpa [haddrs] using hnotNext⟩

private theorem sll_s_heap_ext (ptr : CVal) (xs : List Int) {st₁ st₂ : CState}
    (hheap : st₁.heap = st₂.heap) :
    sll_s ptr xs st₁ ↔ sll_s ptr xs st₂ := by
  cases st₁ with
  | mk heap env₁ next₁ mem₁ allocs₁ =>
      cases st₂ with
      | mk heap' env₂ next₂ mem₂ allocs₂ =>
          simp at hheap
          cases hheap
          simpa using sll_s_same_heap ptr xs heap env₁ env₂ next₁ next₂ mem₁ mem₂ allocs₁ allocs₂

private theorem stackCall_findAlloc (st : CState) (base : Nat) (value : Int) (head : CVal) :
    (stackCalleeFinalState st base value head).findAllocByBlock (stackCallAlloc st base).block =
      some (stackCallAlloc st base) := by
  rw [CState.findAllocByBlock, stackCalleeFinalState_allocs]
  simp [stackCallAlloc]

private theorem stackCall_read_data (st : CState) (base : Nat) (value : Int) (head : CVal)
    (hblock : st.mem.nextBlock ≠ 0) :
    (stackCallState st base value head).readPtr (stackCallPtr st) = some (.int value) := by
  have hfind :
      (stackCallState st base value head).findAllocByBlock (stackCallAlloc st base).block =
        some (stackCallAlloc st base) := by
    simpa [stackCallState, restoreCallerState] using stackCall_findAlloc st base value head
  have hresolve :
      (stackCallState st base value head).resolvePtr (stackCallPtr st) = some base := by
    simpa [stackCallPtr, stackCallAlloc] using
      (CState.resolvePtr_tracked (stackCallState st base value head) (stackCallAlloc st base) 0 hfind hblock (by decide : 0 < 2))
  rw [CState.readPtr, hresolve]
  simp [CState.readCell, stackCallState, restoreCallerState, stackCalleeFinalState_heap, stackCallHeap]

private theorem stackCall_read_next (st : CState) (base : Nat) (value : Int) (head : CVal)
    (hblock : st.mem.nextBlock ≠ 0) :
    (stackCallState st base value head).readPtr { block := (stackCallPtr st).block, offset := (stackCallPtr st).offset + 1 } =
      some head := by
  have hfind :
      (stackCallState st base value head).findAllocByBlock (stackCallAlloc st base).block =
        some (stackCallAlloc st base) := by
    simpa [stackCallState, restoreCallerState] using stackCall_findAlloc st base value head
  have hresolve :
      (stackCallState st base value head).resolvePtr
          { block := (stackCallPtr st).block, offset := (stackCallPtr st).offset + 1 } =
        some (base + 1) := by
    simpa [stackCallPtr, stackCallAlloc] using
      (CState.resolvePtr_tracked (stackCallState st base value head) (stackCallAlloc st base) 1 hfind hblock (by decide : 1 < 2))
  rw [CState.readPtr, hresolve]
  simp [CState.readCell, stackCallState, restoreCallerState, stackCalleeFinalState_heap, stackCallHeap]

theorem makeStackNode_execCall_exact (base : Nat) (value : Int) (head : CVal) :
    ∀ st,
      st.lookupVar "value" = some (.int value) →
      st.lookupVar "head" = some head →
      st.nextAddr = base →
      st.mem.nextBlock ≠ 0 →
      execCall (stackFunEnvAt base value head) 10 "make_stack_node" [.var "value", .var "head"] st =
        some (CVal.ptrAddr (stackCallPtr st), stackCallState st base value head) := by
  intro st hvalue hhead hbase hblock
  let entry : CState := callEntryState st (makeStackNodeSpecAt base value head) [.int value, head]
  let block := st.mem.nextBlock
  let ptr : PtrVal := { block := block, offset := 0 }
  let st1 := entry.allocCells "node" 2
  let st2 := st1.withHeap (st1.heap.write base (.int value))
  let st3 := st2.withHeap (st2.heap.write (base + 1) head)
  have hallocfresh :
      (st.mem.alloc 0 (Int.ofNat 2) .Freeable).1 = block := by
    simpa [block] using
      (Mem.alloc_fresh st.mem 0 (Int.ofNat 2) .Freeable
        ((st.mem.alloc 0 (Int.ofNat 2) .Freeable).1)
        ((st.mem.alloc 0 (Int.ofNat 2) .Freeable).2) rfl)
  have hallocfresh2 :
      (st.mem.alloc 0 2 .Freeable).1 = block := by
    simpa [block] using
      (Mem.alloc_fresh st.mem 0 2 .Freeable
        ((st.mem.alloc 0 2 .Freeable).1)
        ((st.mem.alloc 0 2 .Freeable).2) rfl)
  have hbind :
      bindCallEnv (makeStackNodeSpecAt base value head).params [.int value, head] =
        [("value", .int value), ("head", head)] := by
    rfl
  have hentryValue : entry.lookupVar "value" = some (.int value) := by
    simp [entry, callEntryState, hbind, CState.lookupVar, List.lookup]
  have hentryHead : entry.lookupVar "head" = some head := by
    simp [entry, callEntryState, hbind, CState.lookupVar, List.lookup]
  have hvalue1 : st1.lookupVar "value" = some (.int value) := by
    simpa [st1, CState.lookupVar, CState.allocCells] using hentryValue
  have hhead2 : st2.lookupVar "head" = some head := by
    simpa [st2, CState.lookupVar, CState.withHeap] using hentryHead
  have hnode1 : st1.lookupVar "node" = some (CVal.ptrAddr ptr) := by
    simp [st1, entry, CState.lookupVar, CState.allocCells, ptr, block, CVal.ptrAddr, hallocfresh2]
  have hnode2 : st2.lookupVar "node" = some (CVal.ptrAddr ptr) := by
    simpa [st2, CState.lookupVar, CState.withHeap] using hnode1
  have hnode3 : st3.lookupVar "node" = some (CVal.ptrAddr ptr) := by
    simpa [st3, CState.lookupVar, CState.withHeap] using hnode2
  have hEvalValue1 : evalExpr (.var "value") st1 = some (.int value) := by
    simpa [evalExpr] using hvalue1
  have hEvalHead2 : evalExpr (.var "head") st2 = some head := by
    simpa [evalExpr] using hhead2
  have hEvalNode1 : evalExpr (.var "node") st1 = some (CVal.ptrAddr ptr) := by
    simpa [evalExpr] using hnode1
  have hEvalNode2 : evalExpr (.var "node") st2 = some (CVal.ptrAddr ptr) := by
    simpa [evalExpr] using hnode2
  have hfind1 : st1.findAllocByBlock block = some { base := base, block := block, cells := 2 } := by
    simp [st1, entry, CState.findAllocByBlock, CState.allocCells, hbase, block, hallocfresh2]
  have hResolveData : st1.resolvePtr ptr = some base := by
    simpa [ptr, block, hbase] using
      (CState.resolvePtr_tracked st1 { base := base, block := block, cells := 2 } 0 hfind1 hblock (by decide : 0 < 2))
  have hWriteData : st1.writePtr ptr (.int value) = some st2 := by
    simp [CState.writePtr, st2, hResolveData]
  have hSlotData : PtrVal.addOffset ptr (Int.ofNat (fieldOffset "data")) = some ptr := by
    simp [PtrVal.addOffset, Addr.addOffset, fieldOffset, ptr]
  have hMapWriteData :
      Option.map ExecResult.normal (st1.writePtr ptr (.int value)) = some (.normal st2) := by
    rw [hWriteData]
    rfl
  have hfind2 : st2.findAllocByBlock block = some { base := base, block := block, cells := 2 } := by
    simp [st2, st1, entry, CState.findAllocByBlock, CState.allocCells, CState.withHeap, hbase, block, hallocfresh2]
  have hResolveNext :
      st2.resolvePtr { block := block, offset := 1 } = some (base + 1) := by
    simpa [block, hbase] using
      (CState.resolvePtr_tracked st2 { base := base, block := block, cells := 2 } 1 hfind2 hblock (by decide : 1 < 2))
  have hWriteNext : st2.writePtr { block := block, offset := 1 } head = some st3 := by
    simp [CState.writePtr, st3, hResolveNext]
  have hSlotNext :
      PtrVal.addOffset ptr (Int.ofNat (fieldOffset "next")) = some { block := block, offset := 1 } := by
    simp [PtrVal.addOffset, Addr.addOffset, fieldOffset, ptr, block]
  have hMapWriteNext :
      Option.map ExecResult.normal (st2.writePtr { block := block, offset := 1 } head) = some (.normal st3) := by
    rw [hWriteNext]
    rfl
  have hEvalRet : evalExpr (.var "node") st3 = some (CVal.ptrAddr ptr) := by
    simpa [evalExpr] using hnode3
  have hExecAlloc :
      execStmt 9 (.alloc "node" 2) entry = some (.normal st1) := by
    simp [execStmt, st1]
  have hExecAssignData :
      execStmt 8 (.assign (.fieldAccess (.var "node") "data") (.var "value")) st1 =
        some (.normal st2) := by
    simp [execStmt, hEvalValue1, hnode1, CVal.ptrAddr]
    simpa [ptr, PtrVal.addOffset, Addr.addOffset, fieldOffset] using hMapWriteData
  have hExecAssignNext :
      execStmt 7 (.assign (.fieldAccess (.var "node") "next") (.var "head")) st2 =
        some (.normal st3) := by
    simp [execStmt, hEvalHead2, hnode2, CVal.ptrAddr]
    simpa [ptr, PtrVal.addOffset, Addr.addOffset, fieldOffset] using hMapWriteNext
  have hExecRetNode :
      execStmt 7 (.ret (.var "node")) st3 = some (.returned (CVal.ptrAddr ptr) st3) := by
    simp [execStmt, hEvalRet]
  have hRetNodeRaw :
      (st3.lookupVar "node").bind (fun v => some (ExecResult.returned v st3)) =
        some (ExecResult.returned (CVal.ptrAddr ptr) st3) := by
    simpa [execStmt] using hExecRetNode
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
  have hExecTail :
      execStmt 8 (.seq (.assign (.fieldAccess (.var "node") "next") (.var "head")) (.ret (.var "node"))) st2 =
        some (.returned (CVal.ptrAddr ptr) st3) := by
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
            | ExecResult.normal st' => (st'.lookupVar "node").bind (fun v => some (ExecResult.returned v st'))
            | ExecResult.returned v st' => some (ExecResult.returned v st')) =
          some (ExecResult.returned (CVal.ptrAddr ptr) st3) := by
      rw [hAssignNextRaw]
      exact hRetNodeRaw
    simpa [execStmt] using hSeqRaw
  have hAssignDataRaw :
      ((st1.lookupVar "value").bind fun v =>
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
          (.seq (.assign (.fieldAccess (.var "node") "data") (.var "value"))
            (.seq (.assign (.fieldAccess (.var "node") "next") (.var "head")) (.ret (.var "node"))))
          st1 =
        some (.returned (CVal.ptrAddr ptr) st3) := by
    have hSeqRaw :
        (((st1.lookupVar "value").bind fun v =>
            (st1.lookupVar "node").bind fun pv =>
              match pv with
              | .ptr block offset =>
                  (PtrVal.addOffset { block := block, offset := offset } (Int.ofNat (fieldOffset "data"))).bind
                    fun slot => Option.map ExecResult.normal (st1.writePtr slot v)
              | _ => none).bind
          fun __do_lift =>
            match __do_lift with
            | ExecResult.normal st' =>
                execStmt 8 (.seq (.assign (.fieldAccess (.var "node") "next") (.var "head")) (.ret (.var "node"))) st'
            | ExecResult.returned v st' => some (ExecResult.returned v st')) =
          some (ExecResult.returned (CVal.ptrAddr ptr) st3) := by
      rw [hAssignDataRaw]
      exact hExecTail
    simpa [execStmt] using hSeqRaw
  have hExecBody :
      execStmt 10 makeStackNodeBody entry = some (.returned (CVal.ptrAddr ptr) st3) := by
    have hSeq :
        (match execStmt 9 (.alloc "node" 2) entry with
        | some (.normal st') =>
            execStmt 9
              (.seq (.assign (.fieldAccess (.var "node") "data") (.var "value"))
                (.seq (.assign (.fieldAccess (.var "node") "next") (.var "head")) (.ret (.var "node"))))
              st'
        | some (.returned v st') => some (.returned v st')
        | none => none) =
          some (.returned (CVal.ptrAddr ptr) st3) := by
      rw [hExecAlloc]
      exact hExecAfterAlloc
    simpa [makeStackNodeBody, execStmt] using hSeq
  have hRestore :
      restoreCallerState st st3 = stackCallState st base value head := by
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
  simpa [execCall, stackFunEnvAt, evalArgs, hvalue, hhead, hbase, makeStackNodeSpecAt,
    hRestore, stackCallPtr, block, ptr, CVal.ptrAddr] using hCallBind

theorem stackPushPop_executes_from_state (xs : List Int) (head : CVal) (value : Int) (base : Nat) :
    ∀ st,
      st.lookupVar "head" = some head →
      st.lookupVar "value" = some (.int value) →
      st.nextAddr = base →
      st.mem.nextBlock ≠ 0 →
      sll_s head xs st →
      base ∉ sll_s_addrs head xs st →
      base + 1 ∉ sll_s_addrs head xs st →
      execStmtFull (stackFunEnvAt base value head) 12 stackPushPopBody st =
        some (.returned (.int value) (stackPushPopFinalState st base value head)) := by
  intro st hhead hvalue hbase hblock hsll hfreshData hfreshNext
  have hCall :=
    makeStackNode_execCall_exact base value head st hvalue hhead hbase hblock
  let node := CVal.ptrAddr (stackCallPtr st)
  let stCall := stackCallState st base value head
  let st1 := stCall.updateVar "node" node
  let st2 := st1.updateVar "head" node
  let st3 := st2.updateVar "result" (.int value)
  let st4 := st3.updateVar "head" head
  have hReadData : stCall.readPtr (stackCallPtr st) = some (.int value) := by
    simpa [stCall] using stackCall_read_data st base value head hblock
  have hReadNext :
      stCall.readPtr { block := (stackCallPtr st).block, offset := (stackCallPtr st).offset + 1 } = some head := by
    simpa [stCall] using stackCall_read_next st base value head hblock
  have hReadData2 : st2.readPtr (stackCallPtr st) = some (.int value) := by
    calc
      st2.readPtr (stackCallPtr st) = st1.readPtr (stackCallPtr st) := by
        simpa [st2] using readPtr_updateVar st1 "head" node (stackCallPtr st)
      _ = stCall.readPtr (stackCallPtr st) := by
        simpa [st1] using readPtr_updateVar stCall "node" node (stackCallPtr st)
      _ = some (.int value) := hReadData
  have hReadNext2 :
      st2.readPtr { block := (stackCallPtr st).block, offset := (stackCallPtr st).offset + 1 } = some head := by
    calc
      st2.readPtr { block := (stackCallPtr st).block, offset := (stackCallPtr st).offset + 1 } =
          st1.readPtr { block := (stackCallPtr st).block, offset := (stackCallPtr st).offset + 1 } := by
            simpa [st2] using readPtr_updateVar st1 "head" node
              { block := (stackCallPtr st).block, offset := (stackCallPtr st).offset + 1 }
      _ = stCall.readPtr { block := (stackCallPtr st).block, offset := (stackCallPtr st).offset + 1 } := by
          simpa [st1] using readPtr_updateVar stCall "node" node
            { block := (stackCallPtr st).block, offset := (stackCallPtr st).offset + 1 }
      _ = some head := hReadNext
  have hEvalData : evalExpr (.fieldAccess (.var "head") "data") st2 = some (.int value) := by
    have hHead2 : st2.lookupVar "head" = some node := by
      simpa [st2] using lookupVar_updateVar_eq st1 "head" node
    simpa [evalExpr, evalStaticExpr, hHead2, fieldOffset, PtrVal.addOffset] using hReadData2
  have hEvalNext : evalExpr (.fieldAccess (.var "head") "next") st3 = some head := by
    have hHead3 : st3.lookupVar "head" = some node := by
      calc
        st3.lookupVar "head" = st2.lookupVar "head" := by
          simpa [st3] using lookupVar_updateVar_ne st2 "result" "head" (.int value)
            (by decide : "head" ≠ "result")
        _ = some node := by
          simpa [st2] using lookupVar_updateVar_eq st1 "head" node
    have hReadNext3 :
        st3.readPtr { block := (stackCallPtr st).block, offset := (stackCallPtr st).offset + 1 } = some head := by
      calc
        st3.readPtr { block := (stackCallPtr st).block, offset := (stackCallPtr st).offset + 1 } =
            st2.readPtr { block := (stackCallPtr st).block, offset := (stackCallPtr st).offset + 1 } := by
              simpa [st3] using readPtr_updateVar st2 "result" (.int value)
                { block := (stackCallPtr st).block, offset := (stackCallPtr st).offset + 1 }
        _ = some head := hReadNext2
    simpa [evalExpr, evalStaticExpr, hHead3, fieldOffset, PtrVal.addOffset] using hReadNext3
  have hEvalRet : evalExpr (.var "result") st4 = some (.int value) := by
    calc
      evalExpr (.var "result") st4 = st4.lookupVar "result" := by simp [evalExpr]
      _ = st3.lookupVar "result" := by
        simpa [st4] using lookupVar_updateVar_ne st3 "head" head "result"
          (by decide : "result" ≠ "head")
      _ = some (.int value) := by
        simpa [st3] using lookupVar_updateVar_eq st2 "result" (.int value)
  simp [execStmtFull, stackPushPopBody, hCall, hEvalData, hEvalNext, hEvalRet, stCall, st1, st2, st3, st4,
    node, stackPushPopFinalState]

theorem stackPushPop_correct (xs : List Int) (head : CVal) (value : Int) (base : Nat) :
    ∀ st,
      st.lookupVar "head" = some head →
      st.lookupVar "value" = some (.int value) →
      st.nextAddr = base →
      st.mem.nextBlock ≠ 0 →
      sll_s head xs st →
      base ∉ sll_s_addrs head xs st →
      base + 1 ∉ sll_s_addrs head xs st →
      ∃ st',
        execStmtFull (stackFunEnvAt base value head) 12 stackPushPopBody st =
          some (.returned (.int value) st') ∧
        st'.lookupVar "head" = some head ∧
        st'.lookupVar "value" = some (.int value) ∧
        st'.lookupVar "result" = some (.int value) ∧
        sll_s head xs st' := by
  intro st hhead hvalue hbase hblock hsll hfreshData hfreshNext
  refine ⟨stackPushPopFinalState st base value head, ?_, ?_, ?_, ?_, ?_⟩
  · exact stackPushPop_executes_from_state xs head value base st hhead hvalue hbase hblock hsll hfreshData hfreshNext
  · simp [stackPushPopFinalState]
  · calc
      (stackPushPopFinalState st base value head).lookupVar "value" =
          (stackCallState st base value head).lookupVar "value" := by
            simp [stackPushPopFinalState, lookupVar_updateVar_ne]
      _ = some (.int value) := by
        simpa [stackCallState, restoreCallerState, CState.lookupVar] using hvalue
  · simp [stackPushPopFinalState]
  · let stData : CState := { st with heap := st.heap.write base (.int value) }
    let stFinalHeap : CState := { stData with heap := stData.heap.write (base + 1) head }
    have h1 : sll_s head xs stData := by
      simpa [stData] using sll_s_write_preserves head xs st hsll hfreshData
    have hfreshNext' : base + 1 ∉ sll_s_addrs head xs stData := by
      simpa [stData] using sll_s_addrs_write_eq head xs st hfreshData ▸ hfreshNext
    have h2 : sll_s head xs stFinalHeap := by
      simpa [stFinalHeap, stData] using sll_s_write_preserves head xs stData h1 hfreshNext'
    have hheapFinal :
        stFinalHeap.heap = (stackPushPopFinalState st base value head).heap := by
      simp [stFinalHeap, stData, stackPushPopFinalState, stackCallState, restoreCallerState,
        stackCalleeFinalState_heap, stackCallHeap, CState.updateVar]
    exact (sll_s_heap_ext head xs hheapFinal).mp h2

theorem stackPushPop_executes :
    execStmtFull stackFunEnv 12 stackPushPopBody stackInit =
      some (.returned (.int 5) stackFinal) := by
  native_decide

theorem stack_verified :
    ∃ st',
      execStmtFull stackFunEnv 12 stackPushPopBody stackInit =
        some (.returned (.int 5) st') ∧
      st'.heap.read 500 = some (.int 5) ∧
      st'.heap.read 501 = some .null ∧
      st'.lookupVar "head" = some .null := by
  refine ⟨stackFinal, stackPushPop_executes, ?_, ?_, ?_⟩ <;>
    simp [stackFinal, stackFinalOf, CState.lookupVar]

end HeytingLean.LeanCP.Examples
