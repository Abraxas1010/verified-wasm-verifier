import HeytingLean.LeanCP.Core.Val
import HeytingLean.LeanCP.Core.Perm
import Mathlib.Data.Finmap

/-!
# LeanCP Block Memory Model

Phase 1 foundation for the QCP/VST full-parity project. This memory model is
introduced alongside the existing flat `Heap` so the rest of LeanCP can be
ported incrementally instead of all at once.
-/

namespace HeytingLean.LeanCP

set_option autoImplicit false

/-- Memory chunks supported by load/store. -/
inductive MemChunk where
  | Mint8signed
  | Mint8unsigned
  | Mint16signed
  | Mint16unsigned
  | Mint32
  | Mptr
  deriving DecidableEq, Repr, Inhabited

/-- A memory block: bounds, partial contents, and uniform permission. -/
structure MemBlock where
  lo : Int
  hi : Int
  contents : Finmap (fun _ : Int => CVal)
  perm : Perm
  deriving DecidableEq

instance : Inhabited MemBlock where
  default := {
    lo := 0
    hi := 0
    contents := ∅
    perm := .Nonempty
  }

/-- Block memory: a finite map of blocks plus the next fresh block id. -/
structure Mem where
  blocks : Finmap (fun _ : Nat => MemBlock)
  nextBlock : Nat
  deriving DecidableEq

instance : Inhabited Mem where
  default := {
    blocks := ∅
    nextBlock := 0
  }

namespace Mem

/-- Block-local bounds check. -/
def inBounds (blk : MemBlock) (ofs : Int) : Prop :=
  blk.lo <= ofs ∧ ofs < blk.hi

instance instDecidableInBounds (blk : MemBlock) (ofs : Int) : Decidable (inBounds blk ofs) := by
  unfold inBounds
  infer_instance

/-- Empty block with no initialized contents. -/
def emptyBlock (lo hi : Int) (p : Perm) : MemBlock := {
  lo := lo
  hi := hi
  contents := ∅
  perm := p
}

/-- Allocate a fresh block. -/
def alloc (m : Mem) (lo hi : Int) (p : Perm) : Nat × Mem :=
  let b := m.nextBlock
  let blk := emptyBlock lo hi p
  (b, { blocks := m.blocks.insert b blk, nextBlock := b + 1 })

/-- Free a block if it exists and is freeable. -/
def free (m : Mem) (b : Nat) : Option Mem := do
  let blk ← m.blocks.lookup b
  if Perm.allowsFree blk.perm then
    some { m with blocks := m.blocks.erase b }
  else
    none

/-- Load a value if the block exists, the access is in-bounds, and read permission holds. -/
def load (m : Mem) (_chunk : MemChunk) (b : Nat) (ofs : Int) : Option CVal := do
  let blk ← m.blocks.lookup b
  if _hBounds : inBounds blk ofs then
    if _hRead : Perm.allowsRead blk.perm then
      blk.contents.lookup ofs
    else
      none
  else
    none

/-- Store a value if the block exists, the access is in-bounds, and write permission holds. -/
def store (m : Mem) (_chunk : MemChunk) (b : Nat) (ofs : Int) (v : CVal) : Option Mem := do
  let blk ← m.blocks.lookup b
  if _hBounds : inBounds blk ofs then
    if _hWrite : Perm.allowsWrite blk.perm then
      let blk' := { blk with contents := blk.contents.insert ofs v }
      some { m with blocks := m.blocks.insert b blk' }
    else
      none
  else
    none

theorem alloc_fresh (m : Mem) (lo hi : Int) (p : Perm) (b : Nat) (m' : Mem)
    (h : m.alloc lo hi p = (b, m')) : b = m.nextBlock := by
  unfold alloc at h
  injection h with hb _
  exact hb.symm

theorem load_store_same (m m' : Mem) (chunk : MemChunk) (b : Nat) (ofs : Int)
    (v v' : CVal) (hs : m.store chunk b ofs v = some m')
    (hl : m'.load chunk b ofs = some v') : v' = v := by
  unfold store at hs
  cases hBlk : m.blocks.lookup b with
  | none =>
      simp [hBlk] at hs
  | some blk =>
      by_cases hBounds : inBounds blk ofs
      · by_cases hWrite : Perm.allowsWrite blk.perm
        · simp [hBlk, hBounds, hWrite] at hs
          cases hs
          have hRead : Perm.allowsRead blk.perm := Perm.allowsRead_of_allowsWrite hWrite
          simp [load, hRead, Finmap.lookup_insert] at hl
          exact hl.2.symm
        · simp [hBlk, hBounds, hWrite] at hs
      · simp [hBlk, hBounds] at hs

theorem load_store_other (m m' : Mem) (chunk : MemChunk) (b1 b2 : Nat)
    (ofs1 ofs2 : Int) (v : CVal)
    (hs : m.store chunk b1 ofs1 v = some m')
    (hne : b1 ≠ b2 ∨ ofs1 ≠ ofs2) :
    m'.load chunk b2 ofs2 = m.load chunk b2 ofs2 := by
  unfold store at hs
  cases hBlk : m.blocks.lookup b1 with
  | none =>
      simp [hBlk] at hs
  | some blk =>
      by_cases hBounds : inBounds blk ofs1
      · by_cases hWrite : Perm.allowsWrite blk.perm
        · simp [hBlk, hBounds, hWrite] at hs
          cases hs
          by_cases hb : b2 = b1
          · subst hb
            cases hne with
            | inl hneq =>
                exact (hneq rfl).elim
            | inr hofs =>
                let blk' : MemBlock := { blk with contents := blk.contents.insert ofs1 v }
                have hofs' : ofs2 ≠ ofs1 := by
                  intro hEq
                  exact hofs hEq.symm
                by_cases hB2 : inBounds blk ofs2
                · have hB2' : inBounds blk' ofs2 := by
                    simpa [blk', inBounds] using hB2
                  by_cases hRead : Perm.allowsRead blk.perm
                  · have hRead' : Perm.allowsRead blk'.perm := by
                      simpa [blk'] using hRead
                    simp [load, hBlk, hB2, hB2', hRead, Finmap.lookup_insert, Finmap.lookup_insert_of_ne, blk', hofs']
                  · have hRead' : ¬Perm.allowsRead blk'.perm := by
                      simpa [blk'] using hRead
                    simp [load, hBlk, hB2, hB2', hRead, Finmap.lookup_insert, blk']
                · have hB2' : ¬inBounds blk' ofs2 := by
                    simpa [blk', inBounds] using hB2
                  simp [load, hBlk, hB2, hB2', Finmap.lookup_insert, blk']
          · have hb' : b2 ≠ b1 := hb
            simp [load, Finmap.lookup_insert_of_ne, hb']
        · simp [hBlk, hBounds, hWrite] at hs
      · simp [hBlk, hBounds] at hs

theorem load_free (m m' : Mem) (chunk : MemChunk) (b : Nat) (ofs : Int)
    (hf : m.free b = some m') :
    m'.load chunk b ofs = none := by
  unfold free at hf
  cases hBlk : m.blocks.lookup b with
  | none =>
      simp [hBlk] at hf
  | some blk =>
      by_cases hFree : Perm.allowsFree blk.perm
      · simp [hBlk, hFree] at hf
        cases hf
        simp [load, Finmap.lookup_erase]
      · simp [hBlk, hFree] at hf

theorem alloc_alloc_disjoint
    (m m1 m2 : Mem) (lo1 hi1 lo2 hi2 : Int) (p1 p2 : Perm)
    (b1 b2 : Nat)
    (h1 : m.alloc lo1 hi1 p1 = (b1, m1))
    (h2 : m1.alloc lo2 hi2 p2 = (b2, m2)) :
    b1 ≠ b2 := by
  unfold alloc at h1
  injection h1 with hb1 hm1
  subst b1 m1
  unfold alloc at h2
  injection h2 with hb2 _
  subst b2
  exact Nat.ne_of_lt (Nat.lt_succ_self _)

end Mem
end HeytingLean.LeanCP
