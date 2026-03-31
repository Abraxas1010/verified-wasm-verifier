import HeytingLean.LeanCP.VCG.SWhile
import HeytingLean.LeanCP.Core.VarLemmas
import HeytingLean.LeanCP.Predicates.SLL


/-!
# LeanCP Example: Verified List Reversal

State-sensitive verification of linked-list reversal with a genuine list
invariant. The proof follows the VST/QCP proof shape: establish the split-list
invariant, preserve it across the four-assignment loop body, and discharge the
exit case when the suffix pointer becomes null.
-/

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

set_option linter.unnecessarySimpa false

private theorem sll_s_addrs_updateVar (ptr : CVal) (xs : List Int) (st : CState) (x : String) (v : CVal) :
    sll_s_addrs ptr xs (st.updateVar x v) = sll_s_addrs ptr xs st := by
  induction xs generalizing ptr st with
  | nil =>
      cases ptr <;> simp [sll_s_addrs, ptrBase?]
  | cons h t ih =>
      cases hbase : ptrBase? ptr with
      | none =>
          simp [sll_s_addrs, hbase]
      | some addr =>
          have hheap : (st.updateVar x v).heap = st.heap := rfl
          cases hnext : st.heap.read (Nat.succ addr + 1) <;>
            simp [sll_s_addrs, hbase, hheap, hnext, ih]

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

private theorem ptr_addr_of_ptrBase_some {v : CVal} {addr : Nat}
    (hvPtr : ptrBase? v = some addr) :
    ∃ p : Addr, v = CVal.ptrAddr p ∧ p.block = 0 ∧ p.offset = Int.ofNat (Nat.succ addr) := by
  refine ⟨{ block := 0, offset := Int.ofNat (Nat.succ addr) }, ?_, rfl, rfl⟩
  simpa [CVal.ptrAddr] using ptr_eq_of_ptrBase_some hvPtr

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

private theorem sll_s_updateVar (ptr : CVal) (xs : List Int) (st : CState) (x : String) (v : CVal) :
    sll_s ptr xs (st.updateVar x v) ↔ sll_s ptr xs st := by
  induction xs generalizing ptr st with
  | nil =>
      cases ptr <;> simp [sll_s, ptrBase?]
  | cons h t ih =>
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
          · rcases (sll_s_cons_iff addr h t (st.updateVar x v)).mp hsll with
              ⟨next, hdata, hnext, hrest, hnotData, hnotNext⟩
            exact (sll_s_cons_iff addr h t st).mpr
              ⟨next, hdata, hnext, (ih next st).mp hrest,
                by simpa [sll_s_addrs_updateVar] using hnotData,
                by simpa [sll_s_addrs_updateVar] using hnotNext⟩
          · rcases (sll_s_cons_iff addr h t st).mp hsll with
              ⟨next, hdata, hnext, hrest, hnotData, hnotNext⟩
            exact (sll_s_cons_iff addr h t (st.updateVar x v)).mpr
              ⟨next, hdata, hnext, (ih next st).mpr hrest,
                by simpa [sll_s_addrs_updateVar] using hnotData,
                by simpa [sll_s_addrs_updateVar] using hnotNext⟩

private theorem list_reverse_step (h : Int) (s1 rest : List Int) :
    (h :: s1).reverse ++ rest = s1.reverse ++ (h :: rest) := by
  simp [List.reverse_cons, List.append_assoc]

private theorem resolvePtr_updateVar (st : CState) (x : String) (v : CVal) (ptr : Addr) :
    (st.updateVar x v).resolvePtr ptr = st.resolvePtr ptr := by
  cases st
  rfl

private theorem resolvePtr_withHeap (st : CState) (heap : Heap) (ptr : Addr) :
    (st.withHeap heap).resolvePtr ptr = st.resolvePtr ptr := by
  cases st
  rfl

/-- Operational side-condition for the active suffix of list reversal: every
reachable node pointer and its `next` field slot must resolve through the
current executable pointer semantics. This is the load-bearing bridge between
the old heap-only SLL invariant and the newer pointer-aware execution model. -/
def sll_s_exec : CVal → List Int → CState → Prop
  | .null, [], _ => True
  | .null, _ :: _, _ => False
  | ptr, [], _ => ptr = .null
  | ptr, _ :: rest, st =>
      match ptrBase? ptr, CVal.toAddr? ptr with
      | some addr, some p =>
          let slotPtr : Addr := { block := p.block, offset := p.offset + 1 }
          st.resolvePtr p = some (Nat.succ addr) ∧
          st.resolvePtr slotPtr = some (Nat.succ addr + 1) ∧
          ∃ next : CVal,
            st.heap.read (Nat.succ addr + 1) = some next ∧
            sll_s_exec next rest st
      | _, _ => False

private theorem sll_s_exec_cons_iff (addr : Nat) (x : Int) (rest : List Int) (st : CState) :
    sll_s_exec (.ptr 0 (Int.ofNat (Nat.succ addr))) (x :: rest) st ↔
      st.resolvePtr { block := 0, offset := Int.ofNat (Nat.succ addr) } = some (Nat.succ addr) ∧
        st.resolvePtr { block := 0, offset := Int.ofNat (Nat.succ addr) + 1 } = some (Nat.succ addr + 1) ∧
        ∃ next : CVal,
          st.heap.read (Nat.succ addr + 1) = some next ∧
          sll_s_exec next rest st := by
  have hbase : ptrBase? (.ptr 0 (Int.ofNat (Nat.succ addr))) = some addr := by
    have hnonneg : 0 ≤ ((addr : Int) + 1) := by
      exact Int.add_nonneg (Int.natCast_nonneg _) (by decide)
    simpa [Nat.succ_eq_add_one, ptrBase?, hnonneg]
  constructor <;> intro hs
  · have haddr : CVal.toAddr? (.ptr 0 (Int.ofNat (Nat.succ addr))) =
        some { block := 0, offset := Int.ofNat (Nat.succ addr) } := by
        simp [CVal.toAddr?]
    simpa [sll_s_exec, hbase, haddr] using hs
  · have haddr : CVal.toAddr? (.ptr 0 (Int.ofNat (Nat.succ addr))) =
        some { block := 0, offset := Int.ofNat (Nat.succ addr) } := by
        simp [CVal.toAddr?]
    simpa [sll_s_exec, hbase, haddr] using hs

private theorem sll_s_exec_nonempty_eq_false_of_ptrBase_none
    {ptr : CVal} {h : Int} {t : List Int} {st : CState}
    (hbase : ptrBase? ptr = none) :
    sll_s_exec ptr (h :: t) st = False := by
  cases ptr with
  | null =>
      simp [sll_s_exec, ptrBase?, CVal.toAddr?]
  | int n =>
      simp [sll_s_exec, ptrBase?, CVal.toAddr?] at hbase ⊢
  | uint n sz =>
      simp [sll_s_exec, ptrBase?, CVal.toAddr?] at hbase ⊢
  | undef =>
      simp [sll_s_exec, ptrBase?, CVal.toAddr?] at hbase ⊢
  | structVal fields =>
      simp [sll_s_exec, ptrBase?, CVal.toAddr?] at hbase ⊢
  | unionVal tag val =>
      simp [sll_s_exec, ptrBase?, CVal.toAddr?] at hbase ⊢
  | float v =>
      simp [sll_s_exec, ptrBase?, CVal.toAddr?] at hbase ⊢
  | ptr block offset =>
      by_cases hblock : block = 0
      · subst hblock
        by_cases hnonneg : 0 ≤ offset
        · cases hnat : Int.toNat offset with
          | zero =>
              simp [sll_s_exec, ptrBase?, CVal.toAddr?, hnonneg, hnat]
          | succ addr =>
              simp [ptrBase?, hnonneg, hnat] at hbase
        · simp [sll_s_exec, ptrBase?, CVal.toAddr?, hnonneg]
      · simp [sll_s_exec, ptrBase?, CVal.toAddr?, hblock]

private theorem sll_s_exec_updateVar (ptr : CVal) (xs : List Int) (st : CState) (x : String) (v : CVal) :
    sll_s_exec ptr xs (st.updateVar x v) ↔ sll_s_exec ptr xs st := by
  induction xs generalizing ptr st with
  | nil =>
      cases ptr <;> simp [sll_s_exec, CVal.toAddr?]
  | cons h t ih =>
      cases hbase : ptrBase? ptr with
      | none =>
          constructor <;> intro hs
          · rw [sll_s_exec_nonempty_eq_false_of_ptrBase_none hbase] at hs
            exact False.elim hs
          · rw [sll_s_exec_nonempty_eq_false_of_ptrBase_none hbase] at hs
            exact False.elim hs
      | some addr =>
          have hptr : ptr = .ptr 0 (Int.ofNat (Nat.succ addr)) := ptr_eq_of_ptrBase_some hbase
          subst ptr
          constructor <;> intro hs
          · rcases (sll_s_exec_cons_iff addr h t (st.updateVar x v)).mp hs with
              ⟨hres, hslot, next, hnext, htail⟩
            exact (sll_s_exec_cons_iff addr h t st).mpr
              ⟨by simpa [resolvePtr_updateVar] using hres,
                by simpa [resolvePtr_updateVar] using hslot,
                next, by simpa using hnext, (ih next st).mp htail⟩
          · rcases (sll_s_exec_cons_iff addr h t st).mp hs with
              ⟨hres, hslot, next, hnext, htail⟩
            exact (sll_s_exec_cons_iff addr h t (st.updateVar x v)).mpr
              ⟨by simpa [resolvePtr_updateVar] using hres,
                by simpa [resolvePtr_updateVar] using hslot,
                next, by simpa using hnext, (ih next st).mpr htail⟩

private theorem sll_s_exec_write_preserves
    (ptr : CVal) (xs : List Int) (st : CState) {addr : Nat} {v : CVal}
    (hsExec : sll_s_exec ptr xs st)
    (hnot : addr ∉ sll_s_addrs ptr xs st) :
    sll_s_exec ptr xs (st.withHeap (st.heap.write addr v)) := by
  induction xs generalizing ptr st with
  | nil =>
      cases ptr <;> simpa [sll_s_exec, CVal.toAddr?] using hsExec
  | cons h t ih =>
      cases hbase : ptrBase? ptr with
      | none =>
          rw [sll_s_exec_nonempty_eq_false_of_ptrBase_none hbase] at hsExec
          exact False.elim hsExec
      | some base =>
          have hptr : ptr = .ptr 0 (Int.ofNat (Nat.succ base)) := ptr_eq_of_ptrBase_some hbase
          subst ptr
          rcases (sll_s_exec_cons_iff base h t st).mp hsExec with
            ⟨hres, hslot, next, hnext, htail⟩
          have hbase' : ptrBase? (.ptr 0 (Int.ofNat (Nat.succ base))) = some base := by
            have hnonneg : 0 ≤ ((base : Int) + 1) := by
              exact Int.add_nonneg (Int.natCast_nonneg _) (by decide)
            simpa [Nat.succ_eq_add_one, ptrBase?, hnonneg]
          have haddrs :
              sll_s_addrs (.ptr 0 (Int.ofNat (Nat.succ base))) (h :: t) st =
                insert (Nat.succ base) (insert (Nat.succ base + 1) (sll_s_addrs next t st)) := by
            rw [sll_s_addrs, hbase']
            dsimp
            rw [hnext]
          have hnotTail : addr ∉ sll_s_addrs next t st := by
            intro hmem
            apply hnot
            rw [haddrs]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem)
          have hslotMem :
              Nat.succ base + 1 ∈ sll_s_addrs (.ptr 0 (Int.ofNat (Nat.succ base))) (h :: t) st := by
            rw [haddrs]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
          have hslotNeAddr : Nat.succ base + 1 ≠ addr := by
            intro hEq
            exact hnot (by simpa [hEq] using hslotMem)
          have hnext' :
              (st.withHeap (st.heap.write addr v)).heap.read (Nat.succ base + 1) = some next := by
            have hreadEq :
                (st.withHeap (st.heap.write addr v)).heap.read (Nat.succ base + 1) =
                  st.heap.read (Nat.succ base + 1) := by
              simpa [CState.withHeap] using
                heap_read_write_ne st.heap addr (Nat.succ base + 1) v hslotNeAddr
            exact hreadEq.trans hnext
          exact (sll_s_exec_cons_iff base h t (st.withHeap (st.heap.write addr v))).mpr
            ⟨by simpa [resolvePtr_withHeap] using hres,
              by simpa [resolvePtr_withHeap] using hslot,
              next, hnext', ih next st htail hnotTail⟩

def listRevLoopBody : CStmt :=
  .seq (.assign (.var "t") (.fieldAccess (.var "v") "next"))
    (.seq (.assign (.fieldAccess (.var "v") "next") (.var "w"))
      (.seq (.assign (.var "w") (.var "v"))
        (.assign (.var "v") (.var "t"))))

def listRevProgram : CStmt :=
  .seq (.assign (.var "w") .null)
    (.seq (.assign (.var "v") (.var "p"))
      (.seq (.whileInv (.var "v") HProp.htrue listRevLoopBody)
        (.ret (.var "w"))))

def listRevInv (sigma : List Int) : SProp := fun st =>
  ∃ s1 s2 w v,
    sigma = s1.reverse ++ s2 ∧
    st.lookupVar "w" = some w ∧
    st.lookupVar "v" = some v ∧
    sll_s w s1 st ∧
    sll_s v s2 st ∧
    sll_s_exec v s2 st ∧
    Disjoint (sll_s_addrs w s1 st) (sll_s_addrs v s2 st)

def listRevPost (sigma : List Int) : CVal → SProp := fun _ st =>
  ∃ w, st.lookupVar "w" = some w ∧ sll_s w sigma.reverse st

private theorem listRev_loopFree : LoopFree listRevLoopBody := by
  simp [listRevLoopBody, LoopFree]

private theorem listRev_noReturn : NoReturn listRevLoopBody := by
  simp [listRevLoopBody, NoReturn]

theorem listRev_inv_init (sigma : List Int) (p : CVal) :
    ∀ st, st.lookupVar "p" = some p →
      sll_s p sigma st →
      sll_s_exec p sigma st →
      listRevInv sigma ((st.updateVar "w" .null).updateVar "v" p) := by
  intro st hp hsll hsExec
  refine ⟨[], sigma, .null, p, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · calc
      ((st.updateVar "w" .null).updateVar "v" p).lookupVar "w"
          = (st.updateVar "w" .null).lookupVar "w" := by
              simpa using lookupVar_updateVar_ne (st.updateVar "w" .null) "v" "w" p (by decide : "w" ≠ "v")
      _ = some .null := by
          simpa using lookupVar_updateVar_eq st "w" .null
  · simpa using lookupVar_updateVar_eq (st.updateVar "w" .null) "v" p
  · simp [sll_s]
  · have hsllW : sll_s p sigma (st.updateVar "w" .null) := by
        simpa using (sll_s_updateVar p sigma st "w" .null).2 hsll
    simpa using (sll_s_updateVar p sigma (st.updateVar "w" .null) "v" p).2 hsllW
  · have hsExecW : sll_s_exec p sigma (st.updateVar "w" .null) := by
        simpa using (sll_s_exec_updateVar p sigma st "w" .null).2 hsExec
    simpa using (sll_s_exec_updateVar p sigma (st.updateVar "w" .null) "v" p).2 hsExecW
  · simp [sll_s_addrs]

theorem listRev_inv_preserved (sigma : List Int) :
    ∀ st, listRevInv sigma st →
      (match st.lookupVar "v" with
       | some v => isTruthy v = true
       | none => False) →
      swp listRevLoopBody (fun _ => listRevInv sigma) st := by
  intro st hInv htruth
  rcases hInv with ⟨s1, s2, w, v, hsigma, hw, hv, hsllW, hsllV, hsExecV, hdis⟩
  have hvTruthy : isTruthy v = true := by
    cases hlookup : st.lookupVar "v" with
    | none =>
        simpa [hlookup] using htruth
    | some vv =>
        have hvv : v = vv := Option.some.inj (hv.symm.trans hlookup)
        subst vv
        simpa [hlookup] using htruth
  rcases sll_s_head_truthy hvTruthy hsllV with
    ⟨addr, h, rest, next, hvPtr, hs2, hdata, hnext, hsllRest, hheadNotDataTail, hheadNotNextTail⟩
  rcases ptr_addr_of_ptrBase_some hvPtr with ⟨p, rfl, hblock, hoff⟩
  subst s2
  let slot : Nat := Nat.succ addr + 1
  let st1 := st.updateVar "t" next
  let st2 : CState := st1.withHeap (st1.heap.write slot w)
  let st3 := st2.updateVar "w" (CVal.ptrAddr p)
  let st4 := st3.updateVar "v" next
  have hp : p = { block := 0, offset := Int.ofNat (Nat.succ addr) } := by
    cases p
    cases hblock
    cases hoff
    rfl
  have hnextSlot : st.heap.read slot = some next := by
    simpa [slot] using hnext

  have hheadMemSuffix : Nat.succ addr ∈ sll_s_addrs (CVal.ptrAddr p) (h :: rest) st := by
    have : Nat.succ addr ∈ insert (Nat.succ addr) (insert slot (sll_s_addrs next rest st)) := by
      exact Finset.mem_insert_self _ _
    simpa [slot, sll_s_addrs, hvPtr, hnext] using this
  have hslotMemSuffix : slot ∈ sll_s_addrs (CVal.ptrAddr p) (h :: rest) st := by
    have : slot ∈ insert (Nat.succ addr) (insert slot (sll_s_addrs next rest st)) := by
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    simpa [slot, sll_s_addrs, hvPtr, hnext] using this
  have hdisLeft := Finset.disjoint_left.mp hdis
  have hheadNotPrefix : Nat.succ addr ∉ sll_s_addrs w s1 st := by
    intro hmem
    exact hdisLeft hmem hheadMemSuffix
  have hslotNotPrefix : slot ∉ sll_s_addrs w s1 st := by
    intro hmem
    exact hdisLeft hmem hslotMemSuffix

  have hsExecV0 : sll_s_exec (.ptr 0 (Int.ofNat (Nat.succ addr))) (h :: rest) st := by
    simpa [CVal.ptrAddr, hblock, hoff] using hsExecV
  have hsExecV' :
      st.resolvePtr p = some (Nat.succ addr) ∧
        st.resolvePtr { block := p.block, offset := p.offset + 1 } = some slot ∧
        ∃ next' : CVal, st.heap.read slot = some next' ∧ sll_s_exec next' rest st := by
    simpa [hp, slot] using (sll_s_exec_cons_iff addr h rest st).mp hsExecV0
  rcases hsExecV' with ⟨hResolveHead, hResolveSlot, next', hnextExec, hsExecRest⟩
  have hnextEq : next' = next := by
    exact Option.some.inj (hnextExec.symm.trans hnextSlot)
  subst next'
  have hEvalField : evalExpr (.fieldAccess (.var "v") "next") st = some next := by
    have hReadSlot :
        st.readPtr { block := p.block, offset := p.offset + 1 } = some next := by
      simp [CState.readPtr, hResolveSlot, hnextSlot]
    simpa [evalExpr, evalStaticExpr, hv, CVal.ptrAddr, fieldOffset, PtrVal.addOffset, slot, hblock, hoff] using hReadSlot

  have hsllW1 : sll_s w s1 st1 := by
    simpa [st1] using (sll_s_updateVar w s1 st "t" next).2 hsllW
  have hsllRest1 : sll_s next rest st1 := by
    simpa [st1] using (sll_s_updateVar next rest st "t" next).2 hsllRest
  have hsExecRest1 : sll_s_exec next rest st1 := by
    simpa [st1] using (sll_s_exec_updateVar next rest st "t" next).2 hsExecRest
  have hslotNotPrefix1 : slot ∉ sll_s_addrs w s1 st1 := by
    rw [show sll_s_addrs w s1 st1 = sll_s_addrs w s1 st by
      simpa [st1] using sll_s_addrs_updateVar w s1 st "t" next]
    exact hslotNotPrefix
  have hslotNotTail1 : slot ∉ sll_s_addrs next rest st1 := by
    rw [show sll_s_addrs next rest st1 = sll_s_addrs next rest st by
      simpa [st1] using sll_s_addrs_updateVar next rest st "t" next]
    exact hheadNotNextTail

  have hsllW2 : sll_s w s1 st2 := by
    have hsllRaw :
        sll_s w s1 { st1 with heap := st1.heap.write slot w } :=
      sll_s_write_preserves w s1 st1 hsllW1 hslotNotPrefix1
    simpa [st2, CState.withHeap] using
      (sll_s_setMem w s1 { st1 with heap := st1.heap.write slot w }
        (CState.syncMem (st1.heap.write slot w) st1.allocs st1.mem.nextBlock)).2 hsllRaw
  have hsllRest2 : sll_s next rest st2 := by
    have hsllRaw :
        sll_s next rest { st1 with heap := st1.heap.write slot w } :=
      sll_s_write_preserves next rest st1 hsllRest1 hslotNotTail1
    simpa [st2, CState.withHeap] using
      (sll_s_setMem next rest { st1 with heap := st1.heap.write slot w }
        (CState.syncMem (st1.heap.write slot w) st1.allocs st1.mem.nextBlock)).2 hsllRaw
  have hsExecRest2 : sll_s_exec next rest st2 := by
    simpa [st2, CState.withHeap] using sll_s_exec_write_preserves next rest st1 hsExecRest1 hslotNotTail1

  have hprefixAddrs2 : sll_s_addrs w s1 st2 = sll_s_addrs w s1 st := by
    calc
      sll_s_addrs w s1 st2 = sll_s_addrs w s1 { st1 with heap := st1.heap.write slot w } := by
        simpa [st2, CState.withHeap] using
          sll_s_addrs_setMem w s1 { st1 with heap := st1.heap.write slot w }
            (CState.syncMem (st1.heap.write slot w) st1.allocs st1.mem.nextBlock)
      _ = sll_s_addrs w s1 st1 := by
        exact sll_s_addrs_write_eq w s1 st1 hslotNotPrefix1
      _ = sll_s_addrs w s1 st := by
        simpa [st1] using sll_s_addrs_updateVar w s1 st "t" next
  have hrestAddrs2 : sll_s_addrs next rest st2 = sll_s_addrs next rest st := by
    calc
      sll_s_addrs next rest st2 = sll_s_addrs next rest { st1 with heap := st1.heap.write slot w } := by
        simpa [st2, CState.withHeap] using
          sll_s_addrs_setMem next rest { st1 with heap := st1.heap.write slot w }
            (CState.syncMem (st1.heap.write slot w) st1.allocs st1.mem.nextBlock)
      _ = sll_s_addrs next rest st1 := by
        exact sll_s_addrs_write_eq next rest st1 hslotNotTail1
      _ = sll_s_addrs next rest st := by
        simpa [st1] using sll_s_addrs_updateVar next rest st "t" next

  have hsllW3 : sll_s w s1 st3 := by
    simpa [st3] using (sll_s_updateVar w s1 st2 "w" (CVal.ptrAddr p)).2 hsllW2
  have hsllW4 : sll_s w s1 st4 := by
    have hsllW3' : sll_s w s1 st3 := hsllW3
    simpa [st4] using (sll_s_updateVar w s1 st3 "v" next).2 hsllW3'
  have hsllRest3 : sll_s next rest st3 := by
    simpa [st3] using (sll_s_updateVar next rest st2 "w" (CVal.ptrAddr p)).2 hsllRest2
  have hsllRest4 : sll_s next rest st4 := by
    simpa [st4] using (sll_s_updateVar next rest st3 "v" next).2 hsllRest3
  have hsExecRest3 : sll_s_exec next rest st3 := by
    simpa [st3] using (sll_s_exec_updateVar next rest st2 "w" (CVal.ptrAddr p)).2 hsExecRest2
  have hsExecRest4 : sll_s_exec next rest st4 := by
    simpa [st4] using (sll_s_exec_updateVar next rest st3 "v" next).2 hsExecRest3

  have hprefixAddrs4 : sll_s_addrs w s1 st4 = sll_s_addrs w s1 st := by
    calc
      sll_s_addrs w s1 st4 = sll_s_addrs w s1 st3 := by
        simpa [st4] using sll_s_addrs_updateVar w s1 st3 "v" next
      _ = sll_s_addrs w s1 st2 := by
        simpa [st3] using sll_s_addrs_updateVar w s1 st2 "w" (CVal.ptrAddr p)
      _ = sll_s_addrs w s1 st := hprefixAddrs2
  have hrestAddrs4 : sll_s_addrs next rest st4 = sll_s_addrs next rest st := by
    calc
      sll_s_addrs next rest st4 = sll_s_addrs next rest st3 := by
        simpa [st4] using sll_s_addrs_updateVar next rest st3 "v" next
      _ = sll_s_addrs next rest st2 := by
        simpa [st3] using sll_s_addrs_updateVar next rest st2 "w" (CVal.ptrAddr p)
      _ = sll_s_addrs next rest st := hrestAddrs2

  have hheadNeSlot : Nat.succ addr ≠ slot := by
    simp [slot]
  have hdata4 : st4.heap.read (Nat.succ addr) = some (.int h) := by
    calc
      st4.heap.read (Nat.succ addr) = st2.heap.read (Nat.succ addr) := rfl
      _ = st1.heap.read (Nat.succ addr) := by
        simpa [st2, slot] using heap_read_write_ne st1.heap slot (Nat.succ addr) w hheadNeSlot
      _ = st.heap.read (Nat.succ addr) := rfl
      _ = some (.int h) := hdata
  have hnext4 : st4.heap.read slot = some w := by
    calc
      st4.heap.read slot = st2.heap.read slot := rfl
      _ = some w := by
        simpa [st2, slot] using heap_read_write_eq st1.heap slot w

  have hheadNotPrefix4 : Nat.succ addr ∉ sll_s_addrs w s1 st4 := by
    simpa [hprefixAddrs4] using hheadNotPrefix
  have hslotNotPrefix4 : slot ∉ sll_s_addrs w s1 st4 := by
    simpa [hprefixAddrs4] using hslotNotPrefix

  have hsllNewPrefix : sll_s (CVal.ptrAddr p) (h :: s1) st4 := by
    have hsllNewPrefix' :
        ∃ next : CVal,
          st4.heap.read (Nat.succ addr) = some (.int h) ∧
          st4.heap.read (Nat.succ addr + 1) = some next ∧
          sll_s next s1 st4 ∧
          Nat.succ addr ∉ sll_s_addrs next s1 st4 ∧
          Nat.succ addr + 1 ∉ sll_s_addrs next s1 st4 := by
      refine ⟨w, hdata4, ?_, hsllW4, hheadNotPrefix4, hslotNotPrefix4⟩
      simpa [slot] using hnext4
    simpa [CVal.ptrAddr, sll_s, ptrBase?, hblock, hoff] using hsllNewPrefix'

  have hw4 : st4.lookupVar "w" = some (CVal.ptrAddr p) := by
    calc
      st4.lookupVar "w" = st3.lookupVar "w" := by
        simpa [st4] using lookupVar_updateVar_ne st3 "v" "w" next (by decide : "w" ≠ "v")
      _ = some (CVal.ptrAddr p) := by
        simpa [st3] using lookupVar_updateVar_eq st2 "w" (CVal.ptrAddr p)
  have hv4 : st4.lookupVar "v" = some next := by
    simpa [st4] using lookupVar_updateVar_eq st3 "v" next

  have hsigma4 : sigma = (h :: s1).reverse ++ rest := by
    simpa [list_reverse_step] using hsigma

  have hprefixShape :
      sll_s_addrs (CVal.ptrAddr p) (h :: s1) st4 =
        insert (Nat.succ addr) (insert slot (sll_s_addrs w s1 st)) := by
    simp [slot, sll_s_addrs, hvPtr, hnext4, hprefixAddrs4]
  have hdis4 : Disjoint (sll_s_addrs (CVal.ptrAddr p) (h :: s1) st4) (sll_s_addrs next rest st4) := by
    apply Finset.disjoint_left.mpr
    intro a haPrefix haRest
    have haRestOld : a ∈ sll_s_addrs next rest st := by
      simpa [hrestAddrs4] using haRest
    have haPrefixCases : a = Nat.succ addr ∨ a = slot ∨ a ∈ sll_s_addrs w s1 st := by
      have : a ∈ insert (Nat.succ addr) (insert slot (sll_s_addrs w s1 st)) := by
        simpa [hprefixShape] using haPrefix
      simpa [Finset.mem_insert, slot] using this
    rcases haPrefixCases with rfl | r
    · exact hheadNotDataTail haRestOld
    · rcases r with rfl | haPrefixOld
      · exact hheadNotNextTail haRestOld
      · have haInOldSuffix : a ∈ sll_s_addrs (CVal.ptrAddr p) (h :: rest) st := by
          have : a ∈ insert (Nat.succ addr) (insert slot (sll_s_addrs next rest st)) := by
            exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem haRestOld)
          simpa [slot, sll_s_addrs, hvPtr, hnext] using this
        exact hdisLeft haPrefixOld haInOldSuffix

  have hInv4 : listRevInv sigma st4 := by
    refine ⟨h :: s1, rest, CVal.ptrAddr p, next, hsigma4, hw4, hv4, hsllNewPrefix, hsllRest4, hsExecRest4, hdis4⟩

  have hv1 : st1.lookupVar "v" = some (CVal.ptrAddr p) := by
    calc
      st1.lookupVar "v" = st.lookupVar "v" := by
        simpa [st1] using lookupVar_updateVar_ne st "t" "v" next (by decide : "v" ≠ "t")
      _ = some (CVal.ptrAddr p) := hv
  have hw1 : st1.lookupVar "w" = some w := by
    calc
      st1.lookupVar "w" = st.lookupVar "w" := by
        simpa [st1] using lookupVar_updateVar_ne st "t" "w" next (by decide : "w" ≠ "t")
      _ = some w := hw
  have ht3 : st3.lookupVar "t" = some next := by
    calc
      st3.lookupVar "t" = st2.lookupVar "t" := by
        simpa [st3] using lookupVar_updateVar_ne st2 "w" "t" (CVal.ptrAddr p) (by decide : "t" ≠ "w")
      _ = st1.lookupVar "t" := rfl
      _ = some next := by
        simpa [st1] using lookupVar_updateVar_eq st "t" next

  have hEvalV1 : evalExpr (.var "v") st1 = some (CVal.ptrAddr p) := by
    simpa [evalExpr] using hv1
  have hEvalV2 : evalExpr (.var "v") st2 = some (CVal.ptrAddr p) := by
    simpa [evalExpr] using hv1
  have hEvalW1 : evalExpr (.var "w") st1 = some w := by
    simpa [evalExpr] using hw1
  have hEvalT3 : evalExpr (.var "t") st3 = some next := by
    simpa [evalExpr] using ht3

  have hAssignV : swp (.assign (.var "v") (.var "t")) (fun _ => listRevInv sigma) st3 := by
    simpa [swp, hEvalT3, st4] using hInv4
  have hAssignW : swp (.assign (.var "w") (.var "v"))
      (fun _ => swp (.assign (.var "v") (.var "t")) (fun _ => listRevInv sigma)) st2 := by
    simpa [swp, hEvalV2, st3] using hAssignV
  have hPairField :
      ∃ slotPtr vOld st',
        PtrVal.addOffset p (Int.ofNat (fieldOffset "next")) = some slotPtr ∧
        st1.readPtr slotPtr = some vOld ∧
        st1.writePtr slotPtr w = some st' ∧
        swp (.seq (.assign (.var "w") (.var "v")) (.assign (.var "v") (.var "t")))
          (fun _ => listRevInv sigma) st' := by
    refine ⟨{ block := p.block, offset := p.offset + 1 }, next, st2, ?_, ?_, ?_, hAssignW⟩
    · simpa [fieldOffset, PtrVal.addOffset, Addr.addOffset]
    · have hReadSlot1 :
          st1.readPtr { block := p.block, offset := p.offset + 1 } = some next := by
        simp [CState.readPtr, st1, resolvePtr_updateVar, hResolveSlot, slot]
        exact hnext
      simpa [slot] using hReadSlot1
    · have hWriteSlot1 :
          st1.writePtr { block := p.block, offset := p.offset + 1 } w = some st2 := by
        simp [CState.writePtr, st2, st1, resolvePtr_updateVar, hResolveSlot, slot]
      simpa [slot] using hWriteSlot1
  have hAssignField : swp (.assign (.fieldAccess (.var "v") "next") (.var "w"))
      (fun _ => swp (.seq (.assign (.var "w") (.var "v")) (.assign (.var "v") (.var "t")))
        (fun _ => listRevInv sigma)) st1 := by
    simpa [swp, hEvalV1, hEvalW1] using hPairField
  change swp listRevLoopBody (fun _ => listRevInv sigma) st
  simpa [listRevLoopBody, swp, hEvalField, st1] using hAssignField

theorem listRev_inv_exit (sigma : List Int) :
    ∀ st, listRevInv sigma st →
      st.lookupVar "v" = some .null →
      ∃ w, st.lookupVar "w" = some w ∧ sll_s w sigma.reverse st := by
  intro st hInv hvNull
  rcases hInv with ⟨s1, s2, w, v, hsigma, hw, hv, hsllW, hsllV, _hsExecV, _hdis⟩
  have hvEq : v = .null := by
    exact Option.some.inj (hv.symm.trans hvNull)
  subst v
  have hs2nil : s2 = [] := (sll_s_null_iff s2 st).mp hsllV
  have hsigma' : sigma = s1.reverse := by
    simpa [hs2nil] using hsigma
  have hs1 : sigma.reverse = s1 := by
    calc
      sigma.reverse = (s1.reverse).reverse := by simpa [hsigma']
      _ = s1 := by simp
  refine ⟨w, hw, ?_⟩
  simpa [hs1] using hsllW

theorem listRev_loop_from_state
    (sigma s1 s2 : List Int) (w v : CVal) (st : CState)
    (hsigma : sigma = s1.reverse ++ s2)
    (hw : st.lookupVar "w" = some w)
    (hv : st.lookupVar "v" = some v)
    (hsllW : sll_s w s1 st)
    (hsllV : sll_s v s2 st)
    (hsExecV : sll_s_exec v s2 st)
    (hdis : Disjoint (sll_s_addrs w s1 st) (sll_s_addrs v s2 st)) :
    swhileWP s2.length (.var "v") (listRevInv sigma) listRevLoopBody (listRevPost sigma) st := by
  induction s2 generalizing s1 w v st with
  | nil =>
      have hInv : listRevInv sigma st := by
        exact ⟨s1, [], w, v, hsigma, hw, hv, hsllW, hsllV, hsExecV, hdis⟩
      have hvNull : v = .null := sll_s_nil_ptr_eq_null hsllV
      subst v
      have hEvalCond : evalExpr (.var "v") st = some .null := by
        simpa [evalExpr] using hv
      have hsigma' : sigma = s1.reverse := by
        simpa using hsigma
      have hs1 : sigma.reverse = s1 := by
        calc
          sigma.reverse = (s1.reverse).reverse := by simpa [hsigma']
          _ = s1 := by simp
      have hPost : listRevPost sigma CVal.undef st := by
        refine ⟨w, hw, ?_⟩
        simpa [hs1] using hsllW
      simpa [swhileWP, hEvalCond, isTruthy] using And.intro hInv hPost
  | cons h rest ih =>
      have hInv : listRevInv sigma st := by
        exact ⟨s1, h :: rest, w, v, hsigma, hw, hv, hsllW, hsllV, hsExecV, hdis⟩
      have hvTruthy : isTruthy v = true := sll_s_nonempty_truthy hsllV
      rcases sll_s_head_truthy hvTruthy hsllV with
        ⟨addr, h', rest', next, hvPtr, hs2, hdata, hnext, hsllRest, hheadNotDataTail, hheadNotNextTail⟩
      injection hs2 with hh hrestEq
      subst hh hrestEq
      rcases ptr_addr_of_ptrBase_some hvPtr with ⟨p, rfl, hblock, hoff⟩
      let slot : Nat := Nat.succ addr + 1
      let st1 := st.updateVar "t" next
      let st2 : CState := st1.withHeap (st1.heap.write slot w)
      let st3 := st2.updateVar "w" (CVal.ptrAddr p)
      let st4 := st3.updateVar "v" next
      have hp : p = { block := 0, offset := Int.ofNat (Nat.succ addr) } := by
        cases p
        cases hblock
        cases hoff
        rfl
      have hnextSlot : st.heap.read slot = some next := by
        simpa [slot] using hnext

      have hheadMemSuffix : Nat.succ addr ∈ sll_s_addrs (CVal.ptrAddr p) (h :: rest) st := by
        have : Nat.succ addr ∈ insert (Nat.succ addr) (insert slot (sll_s_addrs next rest st)) := by
          exact Finset.mem_insert_self _ _
        simpa [slot, sll_s_addrs, hvPtr, hnext] using this
      have hslotMemSuffix : slot ∈ sll_s_addrs (CVal.ptrAddr p) (h :: rest) st := by
        have : slot ∈ insert (Nat.succ addr) (insert slot (sll_s_addrs next rest st)) := by
          exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        simpa [slot, sll_s_addrs, hvPtr, hnext] using this
      have hdisLeft := Finset.disjoint_left.mp hdis
      have hheadNotPrefix : Nat.succ addr ∉ sll_s_addrs w s1 st := by
        intro hmem
        exact hdisLeft hmem hheadMemSuffix
      have hslotNotPrefix : slot ∉ sll_s_addrs w s1 st := by
        intro hmem
        exact hdisLeft hmem hslotMemSuffix

      have hsExecV0 : sll_s_exec (.ptr 0 (Int.ofNat (Nat.succ addr))) (h :: rest) st := by
        simpa [CVal.ptrAddr, hblock, hoff] using hsExecV
      have hsExecV' :
          st.resolvePtr p = some (Nat.succ addr) ∧
            st.resolvePtr { block := p.block, offset := p.offset + 1 } = some slot ∧
            ∃ next' : CVal, st.heap.read slot = some next' ∧ sll_s_exec next' rest st := by
        simpa [hp, slot] using (sll_s_exec_cons_iff addr h rest st).mp hsExecV0
      rcases hsExecV' with ⟨hResolveHead, hResolveSlot, next', hnextExec, hsExecRest⟩
      have hnextEq : next' = next := by
        exact Option.some.inj (hnextExec.symm.trans hnextSlot)
      subst next'
      have hEvalCond : evalExpr (.var "v") st = some (CVal.ptrAddr p) := by
        simpa [evalExpr] using hv
      have hEvalField : evalExpr (.fieldAccess (.var "v") "next") st = some next := by
        have hReadSlot :
            st.readPtr { block := p.block, offset := p.offset + 1 } = some next := by
          simp [CState.readPtr, hResolveSlot, hnextSlot]
        simpa [evalExpr, evalStaticExpr, hv, CVal.ptrAddr, fieldOffset, PtrVal.addOffset, slot, hblock, hoff] using hReadSlot

      have hsllW1 : sll_s w s1 st1 := by
        simpa [st1] using (sll_s_updateVar w s1 st "t" next).2 hsllW
      have hsllRest1 : sll_s next rest st1 := by
        simpa [st1] using (sll_s_updateVar next rest st "t" next).2 hsllRest
      have hsExecRest1 : sll_s_exec next rest st1 := by
        simpa [st1] using (sll_s_exec_updateVar next rest st "t" next).2 hsExecRest
      have hslotNotPrefix1 : slot ∉ sll_s_addrs w s1 st1 := by
        rw [show sll_s_addrs w s1 st1 = sll_s_addrs w s1 st by
          simpa [st1] using sll_s_addrs_updateVar w s1 st "t" next]
        exact hslotNotPrefix
      have hslotNotTail1 : slot ∉ sll_s_addrs next rest st1 := by
        rw [show sll_s_addrs next rest st1 = sll_s_addrs next rest st by
          simpa [st1] using sll_s_addrs_updateVar next rest st "t" next]
        exact hheadNotNextTail

      have hsllW2 : sll_s w s1 st2 := by
        have hsllRaw :
            sll_s w s1 { st1 with heap := st1.heap.write slot w } :=
          sll_s_write_preserves w s1 st1 hsllW1 hslotNotPrefix1
        simpa [st2, CState.withHeap] using
          (sll_s_setMem w s1 { st1 with heap := st1.heap.write slot w }
            (CState.syncMem (st1.heap.write slot w) st1.allocs st1.mem.nextBlock)).2 hsllRaw
      have hsllRest2 : sll_s next rest st2 := by
        have hsllRaw :
            sll_s next rest { st1 with heap := st1.heap.write slot w } :=
          sll_s_write_preserves next rest st1 hsllRest1 hslotNotTail1
        simpa [st2, CState.withHeap] using
          (sll_s_setMem next rest { st1 with heap := st1.heap.write slot w }
            (CState.syncMem (st1.heap.write slot w) st1.allocs st1.mem.nextBlock)).2 hsllRaw
      have hsExecRest2 : sll_s_exec next rest st2 := by
        simpa [st2, CState.withHeap] using sll_s_exec_write_preserves next rest st1 hsExecRest1 hslotNotTail1

      have hprefixAddrs2 : sll_s_addrs w s1 st2 = sll_s_addrs w s1 st := by
        calc
          sll_s_addrs w s1 st2 = sll_s_addrs w s1 { st1 with heap := st1.heap.write slot w } := by
            simpa [st2, CState.withHeap] using
              sll_s_addrs_setMem w s1 { st1 with heap := st1.heap.write slot w }
                (CState.syncMem (st1.heap.write slot w) st1.allocs st1.mem.nextBlock)
          _ = sll_s_addrs w s1 st1 := by
            exact sll_s_addrs_write_eq w s1 st1 hslotNotPrefix1
          _ = sll_s_addrs w s1 st := by
            simpa [st1] using sll_s_addrs_updateVar w s1 st "t" next
      have hrestAddrs2 : sll_s_addrs next rest st2 = sll_s_addrs next rest st := by
        calc
          sll_s_addrs next rest st2 = sll_s_addrs next rest { st1 with heap := st1.heap.write slot w } := by
            simpa [st2, CState.withHeap] using
              sll_s_addrs_setMem next rest { st1 with heap := st1.heap.write slot w }
                (CState.syncMem (st1.heap.write slot w) st1.allocs st1.mem.nextBlock)
          _ = sll_s_addrs next rest st1 := by
            exact sll_s_addrs_write_eq next rest st1 hslotNotTail1
          _ = sll_s_addrs next rest st := by
            simpa [st1] using sll_s_addrs_updateVar next rest st "t" next

      have hsllW3 : sll_s w s1 st3 := by
        simpa [st3] using (sll_s_updateVar w s1 st2 "w" (CVal.ptrAddr p)).2 hsllW2
      have hsllW4 : sll_s w s1 st4 := by
        simpa [st4] using (sll_s_updateVar w s1 st3 "v" next).2 hsllW3
      have hsllRest3 : sll_s next rest st3 := by
        simpa [st3] using (sll_s_updateVar next rest st2 "w" (CVal.ptrAddr p)).2 hsllRest2
      have hsllRest4 : sll_s next rest st4 := by
        simpa [st4] using (sll_s_updateVar next rest st3 "v" next).2 hsllRest3
      have hsExecRest3 : sll_s_exec next rest st3 := by
        simpa [st3] using (sll_s_exec_updateVar next rest st2 "w" (CVal.ptrAddr p)).2 hsExecRest2
      have hsExecRest4 : sll_s_exec next rest st4 := by
        simpa [st4] using (sll_s_exec_updateVar next rest st3 "v" next).2 hsExecRest3

      have hprefixAddrs4 : sll_s_addrs w s1 st4 = sll_s_addrs w s1 st := by
        calc
          sll_s_addrs w s1 st4 = sll_s_addrs w s1 st3 := by
            simpa [st4] using sll_s_addrs_updateVar w s1 st3 "v" next
          _ = sll_s_addrs w s1 st2 := by
            simpa [st3] using sll_s_addrs_updateVar w s1 st2 "w" (CVal.ptrAddr p)
          _ = sll_s_addrs w s1 st := hprefixAddrs2
      have hrestAddrs4 : sll_s_addrs next rest st4 = sll_s_addrs next rest st := by
        calc
          sll_s_addrs next rest st4 = sll_s_addrs next rest st3 := by
            simpa [st4] using sll_s_addrs_updateVar next rest st3 "v" next
          _ = sll_s_addrs next rest st2 := by
            simpa [st3] using sll_s_addrs_updateVar next rest st2 "w" (CVal.ptrAddr p)
          _ = sll_s_addrs next rest st := hrestAddrs2

      have hheadNeSlot : Nat.succ addr ≠ slot := by
        simp [slot]
      have hdata4 : st4.heap.read (Nat.succ addr) = some (.int h) := by
        calc
          st4.heap.read (Nat.succ addr) = st2.heap.read (Nat.succ addr) := rfl
          _ = st1.heap.read (Nat.succ addr) := by
            simpa [st2, slot] using heap_read_write_ne st1.heap slot (Nat.succ addr) w hheadNeSlot
          _ = st.heap.read (Nat.succ addr) := rfl
          _ = some (.int h) := hdata
      have hnext4 : st4.heap.read slot = some w := by
        calc
          st4.heap.read slot = st2.heap.read slot := rfl
          _ = some w := by
            simpa [st2, slot] using heap_read_write_eq st1.heap slot w

      have hheadNotPrefix4 : Nat.succ addr ∉ sll_s_addrs w s1 st4 := by
        simpa [hprefixAddrs4] using hheadNotPrefix
      have hslotNotPrefix4 : slot ∉ sll_s_addrs w s1 st4 := by
        simpa [hprefixAddrs4] using hslotNotPrefix

      have hsllNewPrefix : sll_s (CVal.ptrAddr p) (h :: s1) st4 := by
        have hsllNewPrefix' :
            ∃ next : CVal,
              st4.heap.read (Nat.succ addr) = some (.int h) ∧
              st4.heap.read (Nat.succ addr + 1) = some next ∧
              sll_s next s1 st4 ∧
              Nat.succ addr ∉ sll_s_addrs next s1 st4 ∧
              Nat.succ addr + 1 ∉ sll_s_addrs next s1 st4 := by
          refine ⟨w, hdata4, ?_, hsllW4, hheadNotPrefix4, hslotNotPrefix4⟩
          simpa [slot] using hnext4
        simpa [CVal.ptrAddr, sll_s, ptrBase?, hblock, hoff] using hsllNewPrefix'

      have hw4 : st4.lookupVar "w" = some (CVal.ptrAddr p) := by
        calc
          st4.lookupVar "w" = st3.lookupVar "w" := by
            simpa [st4] using lookupVar_updateVar_ne st3 "v" "w" next (by decide : "w" ≠ "v")
          _ = some (CVal.ptrAddr p) := by
            simpa [st3] using lookupVar_updateVar_eq st2 "w" (CVal.ptrAddr p)
      have hv4 : st4.lookupVar "v" = some next := by
        simpa [st4] using lookupVar_updateVar_eq st3 "v" next

      have hsigma4 : sigma = (h :: s1).reverse ++ rest := by
        simpa [list_reverse_step] using hsigma

      have hprefixShape :
          sll_s_addrs (CVal.ptrAddr p) (h :: s1) st4 =
            insert (Nat.succ addr) (insert slot (sll_s_addrs w s1 st)) := by
        simp [slot, sll_s_addrs, hvPtr, hnext4, hprefixAddrs4]
      have hdis4 : Disjoint (sll_s_addrs (CVal.ptrAddr p) (h :: s1) st4) (sll_s_addrs next rest st4) := by
        apply Finset.disjoint_left.mpr
        intro a haPrefix haRest
        have haRestOld : a ∈ sll_s_addrs next rest st := by
          simpa [hrestAddrs4] using haRest
        have haPrefixCases : a = Nat.succ addr ∨ a = slot ∨ a ∈ sll_s_addrs w s1 st := by
          have : a ∈ insert (Nat.succ addr) (insert slot (sll_s_addrs w s1 st)) := by
            simpa [hprefixShape] using haPrefix
          simpa [Finset.mem_insert, slot] using this
        rcases haPrefixCases with rfl | r
        · exact hheadNotDataTail haRestOld
        · rcases r with rfl | haPrefixOld
          · exact hheadNotNextTail haRestOld
          · have haInOldSuffix : a ∈ sll_s_addrs (CVal.ptrAddr p) (h :: rest) st := by
              have : a ∈ insert (Nat.succ addr) (insert slot (sll_s_addrs next rest st)) := by
                exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem haRestOld)
              simpa [slot, sll_s_addrs, hvPtr, hnext] using this
            exact hdisLeft haPrefixOld haInOldSuffix

      have hLoop4 : swhileWP rest.length (.var "v") (listRevInv sigma) listRevLoopBody (listRevPost sigma) st4 := by
        exact ih (h :: s1) (CVal.ptrAddr p) next st4 hsigma4 hw4 hv4 hsllNewPrefix hsllRest4 hsExecRest4 hdis4

      have hv1 : st1.lookupVar "v" = some (CVal.ptrAddr p) := by
        calc
          st1.lookupVar "v" = st.lookupVar "v" := by
            simpa [st1] using lookupVar_updateVar_ne st "t" "v" next (by decide : "v" ≠ "t")
          _ = some (CVal.ptrAddr p) := hv
      have hw1 : st1.lookupVar "w" = some w := by
        calc
          st1.lookupVar "w" = st.lookupVar "w" := by
            simpa [st1] using lookupVar_updateVar_ne st "t" "w" next (by decide : "w" ≠ "t")
          _ = some w := hw
      have ht3 : st3.lookupVar "t" = some next := by
        calc
          st3.lookupVar "t" = st2.lookupVar "t" := by
            simpa [st3] using lookupVar_updateVar_ne st2 "w" "t" (CVal.ptrAddr p) (by decide : "t" ≠ "w")
          _ = st1.lookupVar "t" := rfl
          _ = some next := by
            simpa [st1] using lookupVar_updateVar_eq st "t" next

      have hEvalV1 : evalExpr (.var "v") st1 = some (CVal.ptrAddr p) := by
        simpa [evalExpr] using hv1
      have hEvalV2 : evalExpr (.var "v") st2 = some (CVal.ptrAddr p) := by
        simpa [evalExpr] using hv1
      have hEvalW1 : evalExpr (.var "w") st1 = some w := by
        simpa [evalExpr] using hw1
      have hEvalT3 : evalExpr (.var "t") st3 = some next := by
        simpa [evalExpr] using ht3

      have hAssignV :
          swp (.assign (.var "v") (.var "t"))
            (fun _ => swhileWP rest.length (.var "v") (listRevInv sigma) listRevLoopBody (listRevPost sigma)) st3 := by
        simpa [swp, hEvalT3, st4] using hLoop4
      have hAssignW :
          swp (.assign (.var "w") (.var "v"))
            (fun _ =>
              swp (.assign (.var "v") (.var "t"))
                (fun _ => swhileWP rest.length (.var "v") (listRevInv sigma) listRevLoopBody (listRevPost sigma))) st2 := by
        simpa [swp, hEvalV2, st3] using hAssignV
      have hPairField :
          ∃ slotPtr vOld st',
            PtrVal.addOffset p (Int.ofNat (fieldOffset "next")) = some slotPtr ∧
            st1.readPtr slotPtr = some vOld ∧
            st1.writePtr slotPtr w = some st' ∧
            swp (.seq (.assign (.var "w") (.var "v")) (.assign (.var "v") (.var "t")))
              (fun _ => swhileWP rest.length (.var "v") (listRevInv sigma) listRevLoopBody (listRevPost sigma)) st' := by
        refine ⟨{ block := p.block, offset := p.offset + 1 }, next, st2, ?_, ?_, ?_, hAssignW⟩
        · simpa [fieldOffset, PtrVal.addOffset, Addr.addOffset]
        · have hReadSlot1 :
              st1.readPtr { block := p.block, offset := p.offset + 1 } = some next := by
            simp [CState.readPtr, st1, resolvePtr_updateVar, hResolveSlot, slot]
            exact hnext
          simpa [slot] using hReadSlot1
        · have hWriteSlot1 :
              st1.writePtr { block := p.block, offset := p.offset + 1 } w = some st2 := by
            simp [CState.writePtr, st2, st1, resolvePtr_updateVar, hResolveSlot, slot]
          simpa [slot] using hWriteSlot1
      have hAssignField :
          swp (.assign (.fieldAccess (.var "v") "next") (.var "w"))
            (fun _ =>
              swp (.seq (.assign (.var "w") (.var "v")) (.assign (.var "v") (.var "t")))
                (fun _ => swhileWP rest.length (.var "v") (listRevInv sigma) listRevLoopBody (listRevPost sigma))) st1 := by
        simpa [swp, hEvalV1, hEvalW1] using hPairField
      have hBody :
          swp listRevLoopBody
            (fun _ => swhileWP rest.length (.var "v") (listRevInv sigma) listRevLoopBody (listRevPost sigma)) st := by
        simpa [listRevLoopBody, swp, hEvalField, st1] using hAssignField
      simpa [swhileWP, hEvalCond, hvTruthy] using And.intro hInv hBody

theorem listRev_correct (sigma : List Int) (p : CVal) :
    ∀ st, st.lookupVar "p" = some p →
      sll_s p sigma st →
      sll_s_exec p sigma st →
      ∃ w st',
        execStmt (swhileFuel listRevLoopBody sigma.length + 3) listRevProgram st =
          some (.returned w st') ∧
        sll_s w sigma.reverse st' := by
  intro st hp hsll hsExec
  let st1 := st.updateVar "w" .null
  let st2 := st1.updateVar "v" p

  have hp1 : st1.lookupVar "p" = some p := by
    calc
      st1.lookupVar "p" = st.lookupVar "p" := by
        simpa [st1] using lookupVar_updateVar_ne st "w" "p" CVal.null (by decide : "p" ≠ "w")
      _ = some p := hp
  have hw2 : st2.lookupVar "w" = some .null := by
    calc
      st2.lookupVar "w" = st1.lookupVar "w" := by
        simpa [st2] using lookupVar_updateVar_ne st1 "v" "w" p (by decide : "w" ≠ "v")
      _ = some .null := by
        simpa [st1] using lookupVar_updateVar_eq st "w" .null
  have hv2 : st2.lookupVar "v" = some p := by
    simpa [st2] using lookupVar_updateVar_eq st1 "v" p
  have hsllW2 : sll_s .null [] st2 := by
    simp [sll_s]
  have hsllV1 : sll_s p sigma st1 := by
    simpa [st1] using (sll_s_updateVar p sigma st "w" .null).2 hsll
  have hsllV2 : sll_s p sigma st2 := by
    simpa [st2] using (sll_s_updateVar p sigma st1 "v" p).2 hsllV1
  have hsExecV1 : sll_s_exec p sigma st1 := by
    simpa [st1] using (sll_s_exec_updateVar p sigma st "w" .null).2 hsExec
  have hsExecV2 : sll_s_exec p sigma st2 := by
    simpa [st2] using (sll_s_exec_updateVar p sigma st1 "v" p).2 hsExecV1
  have hdis2 : Disjoint (sll_s_addrs .null [] st2) (sll_s_addrs p sigma st2) := by
    simp [sll_s_addrs]

  have hLoopWP :
      swhileWP sigma.length (.var "v") (listRevInv sigma) listRevLoopBody (listRevPost sigma) st2 := by
    exact listRev_loop_from_state sigma [] sigma .null p st2 (by simp) hw2 hv2 hsllW2 hsllV2 hsExecV2 hdis2

  have hLoopExec :
      ∃ stLoop,
        execStmt (swhileFuel listRevLoopBody sigma.length)
          (.whileInv (.var "v") HProp.htrue listRevLoopBody) st2 = some (.normal stLoop) ∧
        listRevPost sigma CVal.undef stLoop := by
    exact swhileWP_sound (.var "v") (listRevInv sigma) HProp.htrue listRevLoopBody
      listRev_loopFree listRev_noReturn hLoopWP
  rcases hLoopExec with ⟨stLoop, hExecLoop, hPostLoop⟩
  rcases hPostLoop with ⟨w, hwLoop, hsllLoop⟩

  refine ⟨w, stLoop, ?_, hsllLoop⟩
  have hRet :
      execStmt (swhileFuel listRevLoopBody sigma.length) (.ret (.var "w")) stLoop =
        some (.returned w stLoop) := by
    change execStmt (Nat.succ (stmtDepth listRevLoopBody + sigma.length)) (.ret (.var "w")) stLoop =
      some (.returned w stLoop)
    simp [execStmt, evalExpr, evalStaticExpr, hwLoop]
  let loopFuel := swhileFuel listRevLoopBody sigma.length
  have hExecInner :
      execStmt (loopFuel + 1)
        (.seq (.whileInv (.var "v") HProp.htrue listRevLoopBody) (.ret (.var "w"))) st2 =
          some (.returned w stLoop) := by
    change execStmt (loopFuel + 1)
      (.seq (.whileInv (.var "v") HProp.htrue listRevLoopBody) (.ret (.var "w"))) st2 =
        some (.returned w stLoop)
    simp [execStmt]
    rw [hExecLoop]
    simpa [hRet]
  have hExecRest :
      execStmt (loopFuel + 2)
        (.seq (.assign (.var "v") (.var "p"))
          (.seq (.whileInv (.var "v") HProp.htrue listRevLoopBody) (.ret (.var "w")))) st1 =
          some (.returned w stLoop) := by
    change execStmt (Nat.succ (loopFuel + 1))
      (.seq (.assign (.var "v") (.var "p"))
        (.seq (.whileInv (.var "v") HProp.htrue listRevLoopBody) (.ret (.var "w")))) st1 =
          some (.returned w stLoop)
    have hEvalP1 : evalExpr (.var "p") st1 = some p := by
      simpa [evalExpr] using hp1
    simpa [execStmt, hEvalP1, st2] using hExecInner
  change execStmt (Nat.succ (loopFuel + 2)) listRevProgram st =
    some (.returned w stLoop)
  have hEvalNull : evalExpr .null st = some .null := by
    simp [evalExpr, evalStaticExpr]
  simpa [listRevProgram, execStmt, hEvalNull, st1] using hExecRest

end HeytingLean.LeanCP.Examples
