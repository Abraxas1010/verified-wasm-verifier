import HeytingLean.LeanCP.Core.Val
import HeytingLean.LeanCP.Core.Mem
import Mathlib.Data.Finmap
import Mathlib.Data.Finset.Max

/-!
# LeanCP Heap Model

The heap is a finite partial map from addresses (Nat) to C values (CVal).
Built on Mathlib's Finmap with constant value type.
-/

namespace HeytingLean.LeanCP

set_option autoImplicit false

/-- The heap: a finite partial map from natural-number addresses to C values. -/
abbrev Heap := Finmap (fun _ : Nat => CVal)

namespace Heap

/-- The empty heap. -/
def empty : Heap := ∅

instance : EmptyCollection Heap := ⟨empty⟩

/-- Read from the heap. Returns `none` if address is unallocated. -/
def read (h : Heap) (addr : Nat) : Option CVal := h.lookup addr

/-- Write to the heap. Overwrites if present, inserts if not. -/
def write (h : Heap) (addr : Nat) (v : CVal) : Heap := h.insert addr v

/-- Deallocate an address. -/
def free (h : Heap) (addr : Nat) : Heap := h.erase addr

/-- Union of two heaps. -/
def union (h1 h2 : Heap) : Heap := h1 ∪ h2

/-- Reindex flat-heap keys as offsets in block 0.
Kept as a named helper so the Phase 1 memory bridge can be rebuilt
incrementally without changing the flat heap API surface. -/
def offsetKeys (h : Heap) : Finset Int := h.keys.image Int.ofNat

/-- Lookup on the block-0 embedding of a flat heap. -/
def offsetLookup (h : Heap) (ofs : Int) : Option CVal :=
  if 0 ≤ ofs then h.lookup ofs.toNat else none

theorem offsetLookup_isSome (h : Heap) (ofs : Int) :
    (offsetLookup h ofs).isSome ↔ ofs ∈ offsetKeys h := by
  by_cases hnonneg : 0 ≤ ofs
  · simp [offsetLookup, offsetKeys, hnonneg]
    constructor
    · intro hsome
      exact ⟨ofs.toNat, (Finmap.mem_keys).mpr ((Finmap.lookup_isSome).mp hsome), Int.toNat_of_nonneg hnonneg⟩
    · rintro ⟨n, hn, hEq⟩
      have hsome : (h.lookup n).isSome := (Finmap.lookup_isSome).mpr ((Finmap.mem_keys).mp hn)
      have hToNat : ofs.toNat = n := by
        rw [← hEq]
        simp
      rw [hToNat]
      exact hsome
  · simp [offsetLookup, offsetKeys, hnonneg]
    intro n _hn hEq
    apply hnonneg
    simp [← hEq]

/-- Finite offset contents for the block-0 embedding of a flat heap. -/
def toOffsetContents (h : Heap) : Finmap (fun _ : Int => CVal) :=
  (Finmap.keysLookupEquiv (β := fun _ : Int => CVal)).symm
    ⟨(offsetKeys h, offsetLookup h), offsetLookup_isSome h⟩

/-- Max address present in the flat heap, defaulting to 0 on the empty heap. -/
def maxAddr (h : Heap) : Nat :=
  if hne : h.keys.Nonempty then h.keys.max' hne else 0

/-- Upper bound used for the block-0 embedding. -/
def upperBound (h : Heap) : Int := Int.ofNat (h.maxAddr + 1)

/-- Embed the legacy flat heap into the new block memory model using block 0. -/
def toMem (h : Heap) : Mem :=
  if _hEmpty : h = ∅ then
    { blocks := ∅, nextBlock := 1 }
  else
    let blk : MemBlock := {
      lo := 0
      hi := upperBound h
      contents := toOffsetContents h
      perm := .Writable
    }
    { blocks := (∅ : Finmap (fun _ : Nat => MemBlock)).insert 0 blk, nextBlock := 1 }

/-- Filter nonnegative offsets and reindex them back to natural addresses. -/
def natKeys (c : Finmap (fun _ : Int => CVal)) : Finset Nat :=
  (c.keys.filter fun ofs => 0 ≤ ofs).image Int.toNat

/-- Reconstruct a flat heap from finite offset contents. -/
def ofOffsetContents (c : Finmap (fun _ : Int => CVal)) : Heap :=
  let lookupNat : Nat → Option CVal := fun n => c.lookup (Int.ofNat n)
  let keyWitness : ∀ n, (lookupNat n).isSome ↔ n ∈ natKeys c := by
    intro n
    constructor
    · intro hsome
      apply Finset.mem_image.mpr
      refine ⟨Int.ofNat n, ?_, by simp⟩
      refine Finset.mem_filter.mpr ?_
      constructor
      · exact (Finmap.mem_keys).mpr ((Finmap.lookup_isSome).mp hsome)
      · simp
    · intro hmem
      rcases Finset.mem_image.mp hmem with ⟨ofs, hofs, hEq⟩
      rcases Finset.mem_filter.mp hofs with ⟨hofsKey, hofsnonneg⟩
      have hofsEq : ofs = Int.ofNat n := by
        calc
          ofs = Int.ofNat (Int.toNat ofs) := by symm; exact Int.toNat_of_nonneg hofsnonneg
          _ = Int.ofNat n := by rw [hEq]
      have hsome : (c.lookup ofs).isSome := (Finmap.lookup_isSome).mpr ((Finmap.mem_keys).mp hofsKey)
      rw [hofsEq] at hsome
      simpa [lookupNat] using hsome
  (Finmap.keysLookupEquiv (β := fun _ : Nat => CVal)).symm
    ⟨(natKeys c, lookupNat), keyWitness⟩

/-- Project block 0 of a block memory back to a flat heap view. -/
def ofMemBlock0 (m : Mem) : Heap :=
  match m.blocks.lookup 0 with
  | some blk => ofOffsetContents blk.contents
  | none => ∅

@[simp] theorem ofOffsetContents_toOffsetContents_lookup (h : Heap) (n : Nat) :
    (ofOffsetContents (toOffsetContents h)).lookup n = h.lookup n := by
  simp [ofOffsetContents, toOffsetContents, offsetLookup]

@[simp] theorem ofOffsetContents_toOffsetContents (h : Heap) :
    ofOffsetContents (toOffsetContents h) = h := by
  apply Finmap.ext_lookup
  intro n
  exact ofOffsetContents_toOffsetContents_lookup h n

@[simp] theorem ofMemBlock0_toMem (h : Heap) : ofMemBlock0 (toMem h) = h := by
  by_cases hEmpty : h = ∅
  · simp [toMem, ofMemBlock0, hEmpty]
  · simp [toMem, ofMemBlock0, hEmpty, ofOffsetContents_toOffsetContents]

-- Key properties (using Finmap.Disjoint directly)
theorem disjoint_comm {h1 h2 : Heap} :
    Finmap.Disjoint h1 h2 ↔ Finmap.Disjoint h2 h1 :=
  Finmap.Disjoint.symm_iff h1 h2

theorem disjoint_empty_left (h : Heap) : Finmap.Disjoint empty h :=
  Finmap.disjoint_empty h

theorem disjoint_empty_right (h : Heap) : Finmap.Disjoint h empty :=
  disjoint_comm.mpr (disjoint_empty_left h)

theorem union_comm_of_disjoint {h1 h2 : Heap} (hd : Finmap.Disjoint h1 h2) :
    union h1 h2 = union h2 h1 :=
  Finmap.union_comm_of_disjoint hd

end Heap

/-- Public exported compatibility bridge from the legacy flat heap into the
Phase 1 block-memory model. These aliases are top-level because some Lean
namespace-resolution paths do not expose the later `Heap.toMem` helper
reliably across downstream modules. -/
def heapToMem (h : Heap) : Mem := Heap.toMem h

/-- Public exported projection of block 0 back into the legacy flat heap. -/
def memBlock0ToHeap (m : Mem) : Heap := Heap.ofMemBlock0 m

@[simp] theorem memBlock0ToHeap_heapToMem (h : Heap) :
    memBlock0ToHeap (heapToMem h) = h := by
  simpa [heapToMem, memBlock0ToHeap] using Heap.ofMemBlock0_toMem h

end HeytingLean.LeanCP
