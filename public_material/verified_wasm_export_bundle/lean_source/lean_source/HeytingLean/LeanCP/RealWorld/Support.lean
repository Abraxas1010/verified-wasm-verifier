import HeytingLean.LeanCP.Examples.ArraySumVerified
import HeytingLean.LeanCP.Examples.StrlenVerified
import HeytingLean.LeanCP.Core.VarLemmas
import Mathlib.Tactic

namespace HeytingLean.LeanCP.RealWorld

open HeytingLean.LeanCP
open HeytingLean.LeanCP.Examples

set_option linter.unnecessarySimpa false

/-- Real-world byte segment predicate: contiguous integer cells. -/
abbrev bytesAt_s (base : Nat) (vals : List Int) : SProp :=
  arrayAt_s base vals

/-- Re-export the read-only null-terminated string predicate on the real-world
surface. -/
abbrev stringAt_s (base : Nat) (chars : List Int) : SProp :=
  Examples.stringAt_s base chars

theorem bytesAt_s_updateVar (base : Nat) (vals : List Int) (st : CState)
    (x : String) (v : CVal) :
    bytesAt_s base vals (st.updateVar x v) ↔ bytesAt_s base vals st := by
  rfl

theorem stringAt_s_updateVar (base : Nat) (chars : List Int) (st : CState)
    (x : String) (v : CVal) :
    stringAt_s base chars (st.updateVar x v) ↔ stringAt_s base chars st := by
  rfl

/-- Prefix-write predicate used by `memset`/`bzero`. -/
def filled_s (base len : Nat) (fill : Int) : SProp := fun st =>
  ∀ i, i < len → st.heap.read (base + i) = some (.int fill)

theorem filled_s_updateVar (base len : Nat) (fill : Int) (st : CState)
    (x : String) (v : CVal) :
    filled_s base len fill (st.updateVar x v) ↔ filled_s base len fill st := by
  rfl

/-- Buffer-existence predicate for writable ranges. -/
def allocated_s (base len : Nat) : SProp := fun st =>
  ∀ i, i < len → ∃ v, st.heap.read (base + i) = some v

theorem allocated_s_updateVar (base len : Nat) (st : CState)
    (x : String) (v : CVal) :
    allocated_s base len (st.updateVar x v) ↔ allocated_s base len st := by
  rfl

theorem allocated_s_of_bytesAt_s (base : Nat) (vals : List Int) (st : CState)
    (hbytes : bytesAt_s base vals st) :
    allocated_s base vals.length st := by
  intro i hi
  refine ⟨.int vals[i], ?_⟩
  exact hbytes i vals[i] (by simpa [List.getElem?_eq_getElem hi])

theorem allocated_s_write_preserved (st : CState) (base len addr : Nat) (v : CVal)
    (halloc : allocated_s base len st) :
    allocated_s base len (st.withHeap (st.heap.write addr v)) := by
  intro i hi
  by_cases haddr : base + i = addr
  · refine ⟨v, ?_⟩
    simpa [haddr] using heap_read_write_eq st.heap addr v
  · rcases halloc i hi with ⟨old, hold⟩
    refine ⟨old, ?_⟩
    calc
      (st.withHeap (st.heap.write addr v)).heap.read (base + i)
          = (st.heap.write addr v).read (base + i) := by simp
      _ = st.heap.read (base + i) := by
            simpa using heap_read_write_ne st.heap addr (base + i) v haddr
      _ = some old := hold

/-- Destination/source agreement on the first `len` cells. -/
def copiedPrefix_s (dstBase srcBase len : Nat) : SProp := fun st =>
  ∀ i, i < len → st.heap.read (dstBase + i) = st.heap.read (srcBase + i)

theorem copiedPrefix_s_updateVar (dstBase srcBase len : Nat) (st : CState)
    (x : String) (v : CVal) :
    copiedPrefix_s dstBase srcBase len (st.updateVar x v) ↔
      copiedPrefix_s dstBase srcBase len st := by
  rfl

/-- Non-overlap assumption for `memcpy`. -/
def disjointRanges (base1 len1 base2 len2 : Nat) : Prop :=
  base1 + len1 ≤ base2 ∨ base2 + len2 ≤ base1

theorem disjointRanges_symm {base1 len1 base2 len2 : Nat} :
    disjointRanges base1 len1 base2 len2 →
      disjointRanges base2 len2 base1 len1 := by
  intro h
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem disjointRanges_index_ne {base1 len1 base2 len2 i j : Nat}
    (hdisj : disjointRanges base1 len1 base2 len2)
    (hi : i < len1) (hj : j < len2) :
    base1 + i ≠ base2 + j := by
  intro heq
  rcases hdisj with h | h
  · omega
  · omega

theorem filled_s_succ_of_write (st : CState) (base k : Nat) (fill : Int)
    (hprefix : filled_s base k fill st) :
    filled_s base (k + 1) fill (st.withHeap (st.heap.write (base + k) (.int fill))) := by
  intro i hi
  by_cases hik : i = k
  · subst hik
    simpa using heap_read_write_eq st.heap (base + k) (.int fill)
  · have hik' : i ≠ k := hik
    have hiklt : i < k := by omega
    calc
      (st.withHeap (st.heap.write (base + k) (.int fill))).heap.read (base + i)
          = (st.heap.write (base + k) (.int fill)).read (base + i) := by simp
      _ = st.heap.read (base + i) := by
            apply heap_read_write_ne
            omega
      _ = some (.int fill) := hprefix i hiklt

theorem copiedPrefix_s_succ_of_write (st : CState) (dstBase srcBase k : Nat)
    (v : Int) (hprefix : copiedPrefix_s dstBase srcBase k st)
    (hsrc : st.heap.read (srcBase + k) = some (.int v))
    (hstable : ∀ i, i < k + 1 → dstBase + k ≠ srcBase + i) :
    copiedPrefix_s dstBase srcBase (k + 1)
      (st.withHeap (st.heap.write (dstBase + k) (.int v))) := by
  intro i hi
  by_cases hik : i = k
  · subst hik
    calc
      (st.withHeap (st.heap.write (dstBase + i) (.int v))).heap.read (dstBase + i)
          = (st.heap.write (dstBase + i) (.int v)).read (dstBase + i) := by simp
      _ = some (.int v) := by simpa using heap_read_write_eq st.heap (dstBase + i) (.int v)
      _ = st.heap.read (srcBase + i) := hsrc.symm
      _ = (st.withHeap (st.heap.write (dstBase + i) (.int v))).heap.read (srcBase + i) := by
            calc
              st.heap.read (srcBase + i) = (st.heap.write (dstBase + i) (.int v)).read (srcBase + i) := by
                symm
                apply heap_read_write_ne
                exact (hstable i hi).symm
              _ = (st.withHeap (st.heap.write (dstBase + i) (.int v))).heap.read (srcBase + i) := by
                simp
  · have hiklt : i < k := by omega
    calc
      (st.withHeap (st.heap.write (dstBase + k) (.int v))).heap.read (dstBase + i)
          = (st.heap.write (dstBase + k) (.int v)).read (dstBase + i) := by simp
      _ = st.heap.read (dstBase + i) := by
            apply heap_read_write_ne
            omega
      _ = st.heap.read (srcBase + i) := hprefix i hiklt
      _ = (st.withHeap (st.heap.write (dstBase + k) (.int v))).heap.read (srcBase + i) := by
            calc
              st.heap.read (srcBase + i) = (st.heap.write (dstBase + k) (.int v)).read (srcBase + i) := by
                symm
                apply heap_read_write_ne
                exact (hstable i hi).symm
              _ = (st.withHeap (st.heap.write (dstBase + k) (.int v))).heap.read (srcBase + i) := by
                simp

end HeytingLean.LeanCP.RealWorld
