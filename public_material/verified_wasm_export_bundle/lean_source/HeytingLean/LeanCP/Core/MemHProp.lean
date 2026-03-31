import HeytingLean.LeanCP.Core.Mem

/-!
# LeanCP Memory Propositions

Separation-logic assertions over the new block-based `Mem` model. This is the
Phase 1 downstream consumer of `Core.Mem`, introduced alongside the legacy
flat-heap `HProp` layer so the rest of LeanCP can be ported incrementally.
-/

namespace HeytingLean.LeanCP

set_option autoImplicit false

/-- Heap propositions over the block-based memory model. -/
def MemHProp := Mem → Prop

namespace MemHProp

/-- Empty memory assertion: no allocated blocks. -/
def emp : MemHProp := fun m => m.blocks = ∅

/-- Exact single-cell memory block assertion. -/
def pointsTo (block : Nat) (offset : Int) (v : CVal) : MemHProp := fun m =>
  let blk : MemBlock := {
    lo := offset
    hi := offset + 1
    contents := (∅ : Finmap (fun _ : Int => CVal)).insert offset v
    perm := .Writable
  }
  m.blocks = (∅ : Finmap (fun _ : Nat => MemBlock)).insert block blk

/-- Separating conjunction over block-based memory. -/
def sep (P Q : MemHProp) : MemHProp := fun m =>
  ∃ b1 b2, Finmap.Disjoint b1 b2 ∧
    m.blocks = b1 ∪ b2 ∧
    P { m with blocks := b1 } ∧
    Q { m with blocks := b2 }

/-- Magic wand over block-based memory. -/
def wand (P Q : MemHProp) : MemHProp := fun m =>
  ∀ b', Finmap.Disjoint m.blocks b' →
    P { m with blocks := b' } →
    Q { m with blocks := m.blocks ∪ b' }

/-- Pure assertion lifted to memory propositions. -/
def pure (p : Prop) : MemHProp := fun m => m.blocks = ∅ ∧ p

/-- Memory-agnostic fact assertion. -/
def fact (p : Prop) : MemHProp := fun _ => p

/-- Existential quantification in `MemHProp`. -/
def hexists {α : Type} (P : α → MemHProp) : MemHProp := fun m => ∃ a, P a m

/-- Universal quantification in `MemHProp`. -/
def hforall {α : Type} (P : α → MemHProp) : MemHProp := fun m => ∀ a, P a m

/-- Conjunction on the same memory. -/
def hand (P Q : MemHProp) : MemHProp := fun m => P m ∧ Q m

/-- Disjunction on the same memory. -/
def hor (P Q : MemHProp) : MemHProp := fun m => P m ∨ Q m

def htrue : MemHProp := fun _ => True
def hfalse : MemHProp := fun _ => False

infixl:35 " ∗ₘ " => sep
infixr:25 " -∗ₘ " => wand
notation "⌜ₘ" p "⌝" => pure p

theorem pointsTo_load (block : Nat) (offset : Int) (v : CVal) (m : Mem)
    (hpt : pointsTo block offset v m) :
    m.load .Mint32 block offset = some v := by
  let blk : MemBlock := {
    lo := offset
    hi := offset + 1
    contents := (∅ : Finmap (fun _ : Int => CVal)).insert offset v
    perm := .Writable
  }
  have hEq : m.blocks = (∅ : Finmap (fun _ : Nat => MemBlock)).insert block blk := hpt
  have hLookup : m.blocks.lookup block = some blk := by
    simp [hEq, blk]
  have hBounds : Mem.inBounds blk offset := by
    simp [Mem.inBounds, blk]
  have hRead : Perm.allowsRead blk.perm := by
    simp [blk, Perm.allowsRead]
  simp [Mem.load, hLookup, hBounds, hRead, blk, Finmap.lookup_insert]

end MemHProp
end HeytingLean.LeanCP
