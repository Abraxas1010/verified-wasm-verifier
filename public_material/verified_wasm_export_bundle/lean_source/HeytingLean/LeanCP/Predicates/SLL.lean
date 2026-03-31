import HeytingLean.LeanCP.Core.HProp
import HeytingLean.LeanCP.Core.SProp
import HeytingLean.LeanCP.Core.SepLog
import HeytingLean.LeanCP.Predicates.Store
import Mathlib.Data.Finset.Basic

/-!
# LeanCP Singly-Linked List Predicate

`sll addr vs` relates a pointer `addr` to a logical list `vs`.
Each node occupies two consecutive heap cells:
  - `addr`   ↦ `CVal.int v`    (data field)
  - `addr+1` ↦ `CVal.ptr next` (next pointer, or 0 for null)

Null pointer convention: address 0 represents NULL (empty list).
-/

namespace HeytingLean.LeanCP

/-- Compatibility projection from native pointers to the legacy non-null flat
address shape expected by the original SLL predicates. Returns the predecessor
of the flat address so recursive cases can keep the `addr + 1` presentation. -/
def ptrBase? : CVal → Option Nat
  | .ptr 0 offset =>
      if 0 ≤ offset then
        match Int.toNat offset with
        | 0 => none
        | Nat.succ addr => some addr
      else
        none
  | _ => none

/-- Singly-linked list predicate.
    `sll 0 []` holds on the empty heap.
    `sll addr (v :: rest)` holds on a heap where addr points to the head node. -/
def sll : Nat → List Int → HProp
  | 0, [] => HProp.emp
  | 0, (_ :: _) => HProp.hfalse  -- null pointer can't hold a non-empty list
  | _ + 1, [] => HProp.hfalse  -- non-null pointer must hold data
  | addr + 1, v :: rest =>
      HProp.hexists fun next : Nat =>
        store (addr + 1) (CVal.int v) ∗
        store (addr + 2) (.ptr 0 (Int.ofNat next)) ∗
        sll next rest

-- Fold/unfold lemmas
theorem sll_nil (h : Heap) : sll 0 [] h ↔ h = Heap.empty := by
  simp [sll, HProp.emp]

theorem sll_null_cons (v : Int) (rest : List Int) :
    sll 0 (v :: rest) = HProp.hfalse := by
  simp [sll]

theorem sll_nonnull_nil (addr : Nat) :
    sll (addr + 1) [] = HProp.hfalse := by
  simp [sll]

theorem sll_cons (addr : Nat) (v : Int) (rest : List Int) (h : Heap) :
    sll (addr + 1) (v :: rest) h ↔
      ∃ next : Nat, (store (addr + 1) (CVal.int v) ∗
               store (addr + 2) (.ptr 0 (Int.ofNat next)) ∗
               sll next rest) h := by
  simp [sll, HProp.hexists]

/-- Addresses read by a state-sensitive list segment. -/
def sll_s_addrs : CVal → List Int → CState → Finset Nat
  | .null, [], _ => ∅
  | ptr, _ :: rest, st =>
      match ptrBase? ptr with
      | some addr =>
          let nexts :=
            match st.heap.read (Nat.succ addr + 1) with
            | some next => sll_s_addrs next rest st
            | none => ∅
          insert (Nat.succ addr) (insert (Nat.succ addr + 1) nexts)
      | none => ∅
  | _, _, _ => ∅

/-- State-sensitive SLL predicate.

This is intentionally read-only over the full state: it tracks the heap cells
reachable from the current head pointer and separately requires the current
node's cells not to appear in the tail address set, which rules out local
cycles/overlap inside a segment. -/
def sll_s : CVal → List Int → SProp
  | .null, [] => fun _ => True
  | .null, _ :: _ => fun _ => False
  | ptr, [] => fun _ =>
      match ptrBase? ptr with
      | some _ => False
      | none =>
          match ptr with
          | .null => True
          | _ => False
  | ptr, v :: rest => fun st =>
      match ptrBase? ptr with
      | some addr =>
          ∃ next : CVal,
            st.heap.read (Nat.succ addr) = some (.int v) ∧
            st.heap.read (Nat.succ addr + 1) = some next ∧
            sll_s next rest st ∧
            (Nat.succ addr) ∉ sll_s_addrs next rest st ∧
            (Nat.succ addr + 1) ∉ sll_s_addrs next rest st
      | none => False

private theorem sll_s_cons_none
    {ptr : CVal} {x : Int} {xs : List Int} {st : CState}
    (hbase : ptrBase? ptr = none) :
    ¬ sll_s ptr (x :: xs) st := by
  cases ptr with
  | null =>
      simp [sll_s] at *
  | int n =>
      simp [ptrBase?, sll_s] at hbase ⊢
  | uint n sz =>
      simp [ptrBase?, sll_s] at hbase ⊢
  | undef =>
      simp [ptrBase?, sll_s] at hbase ⊢
  | structVal fields =>
      simp [ptrBase?, sll_s] at hbase ⊢
  | unionVal tag v =>
      simp [ptrBase?, sll_s] at hbase ⊢
  | float v =>
      simp [ptrBase?, sll_s] at hbase ⊢
  | ptr block offset =>
      by_cases hblock : block = 0
      · subst hblock
        by_cases hnonneg : 0 ≤ offset
        · cases hnat : Int.toNat offset with
          | zero =>
              simp [ptrBase?, sll_s, hnonneg, hnat] at hbase ⊢
          | succ addr =>
              simp [ptrBase?, hnonneg, hnat] at hbase
        · simp [ptrBase?, sll_s, hnonneg] at hbase ⊢
      · simp [ptrBase?, sll_s, hblock] at hbase ⊢

private theorem sll_s_cons_some
    {ptr : CVal} {x : Int} {xs : List Int} {st : CState} {addr : Nat}
    (hbase : ptrBase? ptr = some addr) :
    sll_s ptr (x :: xs) st ↔
      st.heap.read (Nat.succ addr) = some (.int x) ∧
        ∃ next : CVal,
          st.heap.read (Nat.succ addr + 1) = some next ∧
            sll_s next xs st ∧
            Nat.succ addr ∉ sll_s_addrs next xs st ∧
            Nat.succ addr + 1 ∉ sll_s_addrs next xs st := by
  cases ptr with
  | null =>
      simp [ptrBase?, sll_s] at hbase
  | int n =>
      simp [ptrBase?, sll_s] at hbase
  | uint n sz =>
      simp [ptrBase?, sll_s] at hbase
  | undef =>
      simp [ptrBase?, sll_s] at hbase
  | structVal fields =>
      simp [ptrBase?, sll_s] at hbase
  | unionVal tag v =>
      simp [ptrBase?, sll_s] at hbase
  | float v =>
      simp [ptrBase?, sll_s] at hbase
  | ptr block offset =>
      by_cases hblock : block = 0
      · subst hblock
        by_cases hnonneg : 0 ≤ offset
        · cases hnat : Int.toNat offset with
          | zero =>
              simp [ptrBase?, sll_s, hnonneg, hnat] at hbase
          | succ addr' =>
              simp [ptrBase?, hnonneg, hnat] at hbase
              cases hbase
              simp [ptrBase?, sll_s, hnonneg, hnat]
        · simp [ptrBase?, sll_s, hnonneg] at hbase
      · simp [ptrBase?, sll_s, hblock] at hbase

theorem ptr_eq_of_ptrBase_some {v : CVal} {addr : Nat}
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

theorem sll_s_addrs_setMem
    (ptr : CVal) (xs : List Int) (st : CState) (m : Mem) :
    sll_s_addrs ptr xs { st with mem := m } = sll_s_addrs ptr xs st := by
  induction xs generalizing ptr st with
  | nil =>
      cases ptr <;> simp [sll_s_addrs, ptrBase?]
  | cons x xs ih =>
      cases hbase : ptrBase? ptr with
      | none =>
          simp [sll_s_addrs, hbase]
      | some addr =>
          cases hnext : st.heap.read (Nat.succ addr + 1) <;>
            simp [sll_s_addrs, hbase, hnext, ih]

theorem sll_s_setMem
    (ptr : CVal) (xs : List Int) (st : CState) (m : Mem) :
    sll_s ptr xs { st with mem := m } ↔ sll_s ptr xs st := by
  induction xs generalizing ptr st with
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
          · exact False.elim (sll_s_cons_none hbase hsll)
          · exact False.elim (sll_s_cons_none hbase hsll)
      | some addr =>
          constructor <;> intro hsll
          · have hsll' :
                ({ st with mem := m }).heap.read (Nat.succ addr) = some (.int x) ∧
                  ∃ next : CVal,
                    ({ st with mem := m }).heap.read (Nat.succ addr + 1) = some next ∧
                    sll_s next xs { st with mem := m } ∧
                    Nat.succ addr ∉ sll_s_addrs next xs { st with mem := m } ∧
                    Nat.succ addr + 1 ∉ sll_s_addrs next xs { st with mem := m } := by
                exact (sll_s_cons_some hbase).mp hsll
            rcases hsll' with ⟨hdata, next, hnext, hrest, hnotData, hnotNext⟩
            have haddrsEq :
                  sll_s_addrs next xs { st with mem := m } = sll_s_addrs next xs st :=
                  sll_s_addrs_setMem next xs st m
            have hsll'' :
                st.heap.read (Nat.succ addr) = some (.int x) ∧
                  ∃ next : CVal,
                    st.heap.read (Nat.succ addr + 1) = some next ∧
                    sll_s next xs st ∧
                    Nat.succ addr ∉ sll_s_addrs next xs st ∧
                    Nat.succ addr + 1 ∉ sll_s_addrs next xs st := by
                exact ⟨hdata, next, hnext, (ih next st).mp hrest,
                  by simpa [haddrsEq] using hnotData,
                  by simpa [haddrsEq] using hnotNext⟩
            exact (sll_s_cons_some hbase).mpr hsll''
          · have hsll' :
                st.heap.read (Nat.succ addr) = some (.int x) ∧
                  ∃ next : CVal,
                    st.heap.read (Nat.succ addr + 1) = some next ∧
                    sll_s next xs st ∧
                    Nat.succ addr ∉ sll_s_addrs next xs st ∧
                    Nat.succ addr + 1 ∉ sll_s_addrs next xs st := by
                exact (sll_s_cons_some hbase).mp hsll
            rcases hsll' with ⟨hdata, next, hnext, hrest, hnotData, hnotNext⟩
            have haddrsEq :
                sll_s_addrs next xs { st with mem := m } = sll_s_addrs next xs st :=
                sll_s_addrs_setMem next xs st m
            have hsll'' :
                ({ st with mem := m }).heap.read (Nat.succ addr) = some (.int x) ∧
                  ∃ next : CVal,
                    ({ st with mem := m }).heap.read (Nat.succ addr + 1) = some next ∧
                    sll_s next xs { st with mem := m } ∧
                    Nat.succ addr ∉ sll_s_addrs next xs { st with mem := m } ∧
                    Nat.succ addr + 1 ∉ sll_s_addrs next xs { st with mem := m } := by
                exact ⟨hdata, next, hnext, (ih next st).mpr hrest,
                  by simpa [haddrsEq] using hnotData,
                  by simpa [haddrsEq] using hnotNext⟩
            exact (sll_s_cons_some hbase).mpr hsll''

theorem sll_s_addrs_updateVar
    (ptr : CVal) (xs : List Int) (st : CState) (x : String) (v : CVal) :
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

theorem sll_s_updateVar
    (ptr : CVal) (xs : List Int) (st : CState) (x : String) (v : CVal) :
    sll_s ptr xs (st.updateVar x v) ↔ sll_s ptr xs st := by
  induction xs generalizing ptr st with
  | nil =>
      cases ptr <;> simp [sll_s, ptrBase?]
  | cons h t ih =>
      cases hbase : ptrBase? ptr with
      | none =>
          constructor <;> intro hsll
          · exact False.elim (sll_s_cons_none hbase hsll)
          · exact False.elim (sll_s_cons_none hbase hsll)
      | some addr =>
          constructor <;> intro hsll
          · rcases (sll_s_cons_some hbase).mp hsll with
              ⟨hdata, next, hnext, hrest, hnotData, hnotNext⟩
            exact (sll_s_cons_some hbase).mpr
              ⟨hdata, next, hnext, (ih next st).mp hrest,
                by simpa [sll_s_addrs_updateVar] using hnotData,
                by simpa [sll_s_addrs_updateVar] using hnotNext⟩
          · rcases (sll_s_cons_some hbase).mp hsll with
              ⟨hdata, next, hnext, hrest, hnotData, hnotNext⟩
            exact (sll_s_cons_some hbase).mpr
              ⟨hdata, next, hnext, (ih next st).mpr hrest,
                by simpa [sll_s_addrs_updateVar] using hnotData,
                by simpa [sll_s_addrs_updateVar] using hnotNext⟩

theorem sll_s_updateVar_preserves
    (ptr : CVal) (xs : List Int) (st : CState) (x : String) (v : CVal)
    (hsll : sll_s ptr xs st) :
    sll_s ptr xs (st.updateVar x v) := by
  exact (sll_s_updateVar ptr xs st x v).2 hsll

theorem sll_s_cons_iff (addr : Nat) (v : Int) (rest : List Int) (st : CState) :
    sll_s (.ptr 0 (Int.ofNat (Nat.succ addr))) (v :: rest) st ↔
      ∃ next : CVal,
        st.heap.read (Nat.succ addr) = some (.int v) ∧
        st.heap.read (Nat.succ addr + 1) = some next ∧
        sll_s next rest st ∧
        (Nat.succ addr) ∉ sll_s_addrs next rest st ∧
        (Nat.succ addr + 1) ∉ sll_s_addrs next rest st := by
  have hbase : ptrBase? (.ptr 0 (Int.ofNat (Nat.succ addr))) = some addr := by
    have hnonneg : 0 ≤ ((addr : Int) + 1) := by
      exact Int.add_nonneg (Int.ofNat_nonneg _) (by decide)
    simp [ptrBase?, Nat.succ_eq_add_one, hnonneg]
  constructor
  · intro hsll
    rcases (sll_s_cons_some hbase).mp hsll with ⟨hdata, next, hnext, hrest, hnotData, hnotNext⟩
    exact ⟨next, hdata, hnext, hrest, hnotData, hnotNext⟩
  · intro hsll
    rcases hsll with ⟨next, hdata, hnext, hrest, hnotData, hnotNext⟩
    exact (sll_s_cons_some hbase).mpr ⟨hdata, next, hnext, hrest, hnotData, hnotNext⟩

theorem sll_s_null_iff (xs : List Int) (st : CState) :
    sll_s .null xs st ↔ xs = [] := by
  cases xs <;> simp [sll_s, ptrBase?]

theorem sll_s_nil_ptr_eq_null {ptr : CVal} {st : CState}
    (hsll : sll_s ptr [] st) : ptr = .null := by
  cases ptr with
  | null =>
      rfl
  | int n =>
      simp [sll_s, ptrBase?] at hsll
  | uint n sz =>
      simp [sll_s, ptrBase?] at hsll
  | undef =>
      simp [sll_s, ptrBase?] at hsll
  | structVal fields =>
      simp [sll_s, ptrBase?] at hsll
  | unionVal tag v =>
      simp [sll_s, ptrBase?] at hsll
  | float v =>
      simp [sll_s, ptrBase?] at hsll
  | ptr block offset =>
      by_cases hblock : block = 0
      · subst hblock
        by_cases hnonneg : 0 ≤ offset
        · cases hnat : Int.toNat offset <;> simp [sll_s, ptrBase?, hnonneg, hnat] at hsll
        · simp [sll_s, ptrBase?, hnonneg] at hsll
      · simp [sll_s, ptrBase?, hblock] at hsll

theorem sll_s_nonempty_truthy {ptr : CVal} {h : Int} {rest : List Int} {st : CState}
    (hsll : sll_s ptr (h :: rest) st) : isTruthy ptr = true := by
  cases ptr with
  | null =>
      simp [sll_s, ptrBase?] at hsll
  | int n =>
      simp [sll_s, ptrBase?] at hsll
  | uint n sz =>
      simp [sll_s, ptrBase?] at hsll
  | undef =>
      simp [sll_s, ptrBase?] at hsll
  | structVal fields =>
      simp [sll_s, ptrBase?] at hsll
  | unionVal tag v =>
      simp [sll_s, ptrBase?] at hsll
  | float v =>
      simp [sll_s, ptrBase?] at hsll
  | ptr block offset =>
      simp [isTruthy]

private theorem heap_read_write_ne
    (h : Heap) (writeAddr readAddr : Nat) (v : CVal) (hneq : readAddr ≠ writeAddr) :
    (h.write writeAddr v).read readAddr = h.read readAddr := by
  simp [Heap.read, Heap.write, Finmap.lookup_insert_of_ne, hneq]

private theorem heap_read_free_ne
    (h : Heap) (freeAddr readAddr : Nat) (hneq : readAddr ≠ freeAddr) :
    (h.free freeAddr).read readAddr = h.read readAddr := by
  simp [Heap.read, Heap.free, Finmap.lookup_erase, hneq]

theorem sll_s_addrs_write_eq
    (ptr : CVal) (xs : List Int) (st : CState) {addr : Nat} {v : CVal}
    (hnot : addr ∉ sll_s_addrs ptr xs st) :
    sll_s_addrs ptr xs { st with heap := st.heap.write addr v } =
      sll_s_addrs ptr xs st := by
  induction xs generalizing ptr st with
  | nil =>
      cases ptr <;> simp [sll_s_addrs, ptrBase?]
  | cons x xs ih =>
      cases hbase : ptrBase? ptr with
      | none =>
          simp [sll_s_addrs, hbase]
      | some base =>
          have hneqNext : addr ≠ Nat.succ base + 1 := by
            intro hEq
            apply hnot
            simp [sll_s_addrs, hbase, hEq]
          cases hnext : st.heap.read (Nat.succ base + 1) with
          | none =>
              have hnext' :
                  ({ st with heap := st.heap.write addr v }).heap.read (Nat.succ base + 1) = none := by
                calc
                  ({ st with heap := st.heap.write addr v }).heap.read (Nat.succ base + 1)
                      = st.heap.read (Nat.succ base + 1) := by
                          simpa using heap_read_write_ne st.heap addr (Nat.succ base + 1) v hneqNext.symm
                  _ = none := hnext
              simp [sll_s_addrs, hbase, hnext, hnext']
          | some next =>
              have hnotRest : addr ∉ sll_s_addrs next xs st := by
                intro hmem
                apply hnot
                simp [sll_s_addrs, hbase, hnext, hmem]
              have hnext' :
                  ({ st with heap := st.heap.write addr v }).heap.read (Nat.succ base + 1) =
                    some next := by
                calc
                  ({ st with heap := st.heap.write addr v }).heap.read (Nat.succ base + 1)
                      = st.heap.read (Nat.succ base + 1) := by
                          simpa using heap_read_write_ne st.heap addr (Nat.succ base + 1) v hneqNext.symm
                  _ = some next := hnext
              simp [sll_s_addrs, hbase, hnext, hnext', ih next st hnotRest]

theorem sll_s_write_preserves
    (ptr : CVal) (xs : List Int) (st : CState)
    (hsll : sll_s ptr xs st) {addr : Nat} {v : CVal}
    (hnot : addr ∉ sll_s_addrs ptr xs st) :
    sll_s ptr xs { st with heap := st.heap.write addr v } := by
  induction xs generalizing ptr st with
  | nil =>
      have hnull : ptr = .null := sll_s_nil_ptr_eq_null hsll
      subst hnull
      simp [sll_s, ptrBase?]
  | cons x xs ih =>
      cases hbase : ptrBase? ptr with
      | none =>
          exact False.elim (sll_s_cons_none hbase hsll)
      | some base =>
          have hsll' :
                st.heap.read (Nat.succ base) = some (.int x) ∧
                  ∃ next : CVal,
                    st.heap.read (Nat.succ base + 1) = some next ∧
                    sll_s next xs st ∧
                    Nat.succ base ∉ sll_s_addrs next xs st ∧
                    Nat.succ base + 1 ∉ sll_s_addrs next xs st := by
                exact (sll_s_cons_some hbase).mp hsll
          rcases hsll' with ⟨hdata, next, hnext, hrest, hheadData, hheadNext⟩
          have hneqData : addr ≠ Nat.succ base := by
            intro hEq
            apply hnot
            simp [sll_s_addrs, hbase, hnext, hEq]
          have hneqNext : addr ≠ Nat.succ base + 1 := by
            intro hEq
            apply hnot
            simp [sll_s_addrs, hbase, hnext, hEq]
          have hnotRest : addr ∉ sll_s_addrs next xs st := by
            intro hmem
            apply hnot
            simp [sll_s_addrs, hbase, hnext, hmem]
          have haddrsEq :
              sll_s_addrs next xs { st with heap := st.heap.write addr v } =
                sll_s_addrs next xs st :=
            sll_s_addrs_write_eq next xs st hnotRest
          have hsll'' :
              ({ st with heap := st.heap.write addr v }).heap.read (Nat.succ base) = some (.int x) ∧
                ∃ next : CVal,
                  ({ st with heap := st.heap.write addr v }).heap.read (Nat.succ base + 1) = some next ∧
                  sll_s next xs { st with heap := st.heap.write addr v } ∧
                  Nat.succ base ∉ sll_s_addrs next xs { st with heap := st.heap.write addr v } ∧
                  Nat.succ base + 1 ∉ sll_s_addrs next xs { st with heap := st.heap.write addr v } := by
            refine ⟨?_, next, ?_, ?_, ?_, ?_⟩
            · calc
                ({ st with heap := st.heap.write addr v }).heap.read (Nat.succ base)
                    = st.heap.read (Nat.succ base) := by
                        simpa using heap_read_write_ne st.heap addr (Nat.succ base) v hneqData.symm
                _ = some (.int x) := hdata
            · calc
                ({ st with heap := st.heap.write addr v }).heap.read (Nat.succ base + 1)
                    = st.heap.read (Nat.succ base + 1) := by
                        simpa using heap_read_write_ne st.heap addr (Nat.succ base + 1) v hneqNext.symm
                _ = some next := hnext
            · exact ih next st hrest hnotRest
            · simpa [haddrsEq] using hheadData
            · simpa [haddrsEq] using hheadNext
          exact (sll_s_cons_some hbase).mpr hsll''

theorem sll_s_addrs_free_eq
    (ptr : CVal) (xs : List Int) (st : CState) {addr : Nat}
    (hnot : addr ∉ sll_s_addrs ptr xs st) :
    sll_s_addrs ptr xs { st with heap := st.heap.free addr } =
      sll_s_addrs ptr xs st := by
  induction xs generalizing ptr st with
  | nil =>
      cases ptr <;> simp [sll_s_addrs, ptrBase?]
  | cons x xs ih =>
      cases hbase : ptrBase? ptr with
      | none =>
          simp [sll_s_addrs, hbase]
      | some base =>
          have hneqNext : addr ≠ Nat.succ base + 1 := by
            intro hEq
            apply hnot
            simp [sll_s_addrs, hbase, hEq]
          cases hnext : st.heap.read (Nat.succ base + 1) with
          | none =>
              have hnext' :
                  ({ st with heap := st.heap.free addr }).heap.read (Nat.succ base + 1) = none := by
                calc
                  ({ st with heap := st.heap.free addr }).heap.read (Nat.succ base + 1)
                      = st.heap.read (Nat.succ base + 1) := by
                          simpa using heap_read_free_ne st.heap addr (Nat.succ base + 1) hneqNext.symm
                  _ = none := hnext
              simp [sll_s_addrs, hbase, hnext, hnext']
          | some next =>
              have hnotRest : addr ∉ sll_s_addrs next xs st := by
                intro hmem
                apply hnot
                simp [sll_s_addrs, hbase, hnext, hmem]
              have hnext' :
                  ({ st with heap := st.heap.free addr }).heap.read (Nat.succ base + 1) =
                    some next := by
                calc
                  ({ st with heap := st.heap.free addr }).heap.read (Nat.succ base + 1)
                      = st.heap.read (Nat.succ base + 1) := by
                          simpa using heap_read_free_ne st.heap addr (Nat.succ base + 1) hneqNext.symm
                  _ = some next := hnext
              simp [sll_s_addrs, hbase, hnext, hnext', ih next st hnotRest]

theorem sll_s_free_preserves
    (ptr : CVal) (xs : List Int) (st : CState)
    (hsll : sll_s ptr xs st) {addr : Nat}
    (hnot : addr ∉ sll_s_addrs ptr xs st) :
    sll_s ptr xs { st with heap := st.heap.free addr } := by
  induction xs generalizing ptr st with
  | nil =>
      have hnull : ptr = .null := sll_s_nil_ptr_eq_null hsll
      subst hnull
      simp [sll_s, ptrBase?]
  | cons x xs ih =>
      cases hbase : ptrBase? ptr with
      | none =>
          exact False.elim (sll_s_cons_none hbase hsll)
      | some base =>
          have hsll' :
                st.heap.read (Nat.succ base) = some (.int x) ∧
                  ∃ next : CVal,
                    st.heap.read (Nat.succ base + 1) = some next ∧
                    sll_s next xs st ∧
                    Nat.succ base ∉ sll_s_addrs next xs st ∧
                    Nat.succ base + 1 ∉ sll_s_addrs next xs st := by
                exact (sll_s_cons_some hbase).mp hsll
          rcases hsll' with ⟨hdata, next, hnext, hrest, hheadData, hheadNext⟩
          have hneqData : addr ≠ Nat.succ base := by
            intro hEq
            apply hnot
            simp [sll_s_addrs, hbase, hnext, hEq]
          have hneqNext : addr ≠ Nat.succ base + 1 := by
            intro hEq
            apply hnot
            simp [sll_s_addrs, hbase, hnext, hEq]
          have hnotRest : addr ∉ sll_s_addrs next xs st := by
            intro hmem
            apply hnot
            simp [sll_s_addrs, hbase, hnext, hmem]
          have haddrsEq :
              sll_s_addrs next xs { st with heap := st.heap.free addr } =
                sll_s_addrs next xs st :=
            sll_s_addrs_free_eq next xs st hnotRest
          have hsll'' :
              ({ st with heap := st.heap.free addr }).heap.read (Nat.succ base) = some (.int x) ∧
                ∃ next : CVal,
                  ({ st with heap := st.heap.free addr }).heap.read (Nat.succ base + 1) = some next ∧
                  sll_s next xs { st with heap := st.heap.free addr } ∧
                  Nat.succ base ∉ sll_s_addrs next xs { st with heap := st.heap.free addr } ∧
                  Nat.succ base + 1 ∉ sll_s_addrs next xs { st with heap := st.heap.free addr } := by
            refine ⟨?_, next, ?_, ?_, ?_, ?_⟩
            · calc
                ({ st with heap := st.heap.free addr }).heap.read (Nat.succ base)
                    = st.heap.read (Nat.succ base) := by
                        simpa using heap_read_free_ne st.heap addr (Nat.succ base) hneqData.symm
                _ = some (.int x) := hdata
            · calc
                ({ st with heap := st.heap.free addr }).heap.read (Nat.succ base + 1)
                    = st.heap.read (Nat.succ base + 1) := by
                        simpa using heap_read_free_ne st.heap addr (Nat.succ base + 1) hneqNext.symm
                _ = some next := hnext
            · exact ih next st hrest hnotRest
            · simpa [haddrsEq] using hheadData
            · simpa [haddrsEq] using hheadNext
          exact (sll_s_cons_some hbase).mpr hsll''

theorem sll_s_addrs_same_heap
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
              simpa [sll_s_addrs, hbase, hnext] using
                congrArg (fun s => insert (Nat.succ addr) (insert (Nat.succ addr + 1) s)) (ih next)

theorem sll_s_same_heap
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
          · exact False.elim (sll_s_cons_none hbase hsll)
          · exact False.elim (sll_s_cons_none hbase hsll)
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

theorem sll_s_heap_ext (ptr : CVal) (xs : List Int) {st₁ st₂ : CState}
    (hheap : st₁.heap = st₂.heap) :
    sll_s ptr xs st₁ ↔ sll_s ptr xs st₂ := by
  cases st₁ with
  | mk heap env₁ next₁ mem₁ allocs₁ =>
      cases st₂ with
      | mk heap' env₂ next₂ mem₂ allocs₂ =>
          simp at hheap
          cases hheap
          simpa using sll_s_same_heap ptr xs heap env₁ env₂ next₁ next₂ mem₁ mem₂ allocs₁ allocs₂

private theorem freeBlock_two (heap : Heap) (base : Nat) :
    freeBlock heap base 2 = (heap.free base).free (base + 1) := by
  have hrange : List.range 2 = [0, 1] := by decide
  simp [freeBlock, hrange]

theorem sll_s_freeCells_preserves
    (ptr : CVal) (xs : List Int) (st : CState)
    (hsll : sll_s ptr xs st) {addr : Nat}
    (hnotData : addr ∉ sll_s_addrs ptr xs st)
    (hnotNext : addr + 1 ∉ sll_s_addrs ptr xs st) :
    sll_s ptr xs (st.freeCells addr 2) := by
  let st1 : CState := { st with heap := st.heap.free addr }
  have hsll1 : sll_s ptr xs st1 := by
    simpa [st1] using sll_s_free_preserves ptr xs st hsll hnotData
  have haddrs1 : sll_s_addrs ptr xs st1 = sll_s_addrs ptr xs st := by
    simpa [st1] using sll_s_addrs_free_eq ptr xs st hnotData
  have hnotNext1 : addr + 1 ∉ sll_s_addrs ptr xs st1 := by
    simpa [haddrs1] using hnotNext
  have hsll2 : sll_s ptr xs { st1 with heap := st1.heap.free (addr + 1) } := by
    simpa [st1] using sll_s_free_preserves ptr xs st1 hsll1 hnotNext1
  have hheap :
      ({ st1 with heap := st1.heap.free (addr + 1) }).heap = (st.freeCells addr 2).heap := by
    simp [st1, CState.freeCells, freeBlock_two]
  exact (sll_s_heap_ext ptr xs hheap).mp hsll2

theorem sll_s_head_truthy
    {ptr : CVal} {xs : List Int} {st : CState}
    (htruth : isTruthy ptr = true) (hsll : sll_s ptr xs st) :
    ∃ addr h rest next,
      ptrBase? ptr = some addr ∧
      xs = h :: rest ∧
      st.heap.read (Nat.succ addr) = some (.int h) ∧
      st.heap.read (Nat.succ addr + 1) = some next ∧
      sll_s next rest st ∧
      (Nat.succ addr) ∉ sll_s_addrs next rest st ∧
      (Nat.succ addr + 1) ∉ sll_s_addrs next rest st := by
  cases xs with
  | nil =>
      have hptr : ptr = .null := sll_s_nil_ptr_eq_null hsll
      subst hptr
      simp [isTruthy] at htruth
  | cons x xs =>
      cases hbase : ptrBase? ptr with
      | none =>
          exact False.elim (sll_s_cons_none hbase hsll)
      | some addr =>
          have hsll' :
                st.heap.read (Nat.succ addr) = some (.int x) ∧
                  ∃ next : CVal,
                    st.heap.read (Nat.succ addr + 1) = some next ∧
                    sll_s next xs st ∧
                    Nat.succ addr ∉ sll_s_addrs next xs st ∧
                    Nat.succ addr + 1 ∉ sll_s_addrs next xs st := by
                exact (sll_s_cons_some hbase).mp hsll
          rcases hsll' with ⟨hdata, next, hnext, hrest, hnotData, hnotNext⟩
          refine ⟨addr, x, xs, next, ?_⟩
          exact ⟨rfl, rfl, hdata, hnext, hrest, hnotData, hnotNext⟩

end HeytingLean.LeanCP
