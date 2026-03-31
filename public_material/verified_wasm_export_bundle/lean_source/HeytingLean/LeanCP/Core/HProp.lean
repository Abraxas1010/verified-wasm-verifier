import HeytingLean.LeanCP.Core.Heap
import HeytingLean.LeanCP.Core.MemHProp

/-!
# LeanCP Heap Propositions

Heap propositions (`HProp`) are predicates over heaps, forming the assertion
language of separation logic. Adapted from SPlean/Theories/HProp.lean
(ported from Lean 4.11 to 4.24).
-/

namespace HeytingLean.LeanCP

/-- Heap propositions: predicates over heaps. -/
def HProp := Heap → Prop

namespace HProp

/-- Empty heap assertion: holds only on the empty heap. -/
def emp : HProp := fun h => h = Heap.empty

/-- Points-to assertion: the heap is exactly the singleton {addr ↦ v}. -/
def pointsTo (addr : Nat) (v : CVal) : HProp :=
  fun h => h = Heap.write Heap.empty addr v

/-- Separating conjunction: P ∗ Q holds on h iff h splits into disjoint h1, h2
    with P h1 and Q h2. THIS IS THE CORE OF SEPARATION LOGIC. -/
def sep (P Q : HProp) : HProp := fun h =>
  ∃ h1 h2, Finmap.Disjoint h1 h2 ∧ h = Heap.union h1 h2 ∧ P h1 ∧ Q h2

/-- Magic wand (separating implication): P -∗ Q holds on h iff for any
    disjoint h' satisfying P, the union h ∪ h' satisfies Q. -/
def wand (P Q : HProp) : HProp := fun h =>
  ∀ h', Finmap.Disjoint h h' → P h' → Q (Heap.union h h')

/-- Pure assertion lifted to HProp (holds on empty heap). -/
def pure (p : Prop) : HProp := fun h => h = Heap.empty ∧ p

/-- Heap-agnostic fact assertion. Use when a proposition should hold on the current heap. -/
def fact (p : Prop) : HProp := fun _ => p

/-- Existential quantification in HProp. -/
def hexists {α : Type} (P : α → HProp) : HProp := fun h => ∃ a, P a h

/-- Universal quantification in HProp. -/
def hforall {α : Type} (P : α → HProp) : HProp := fun h => ∀ a, P a h

/-- Disjunction in HProp (holds on the same heap). -/
def hor (P Q : HProp) : HProp := fun h => P h ∨ Q h

/-- Conjunction in HProp (holds on the same heap — NOT separating). -/
def hand (P Q : HProp) : HProp := fun h => P h ∧ Q h

/-- The always-true heap proposition. -/
def htrue : HProp := fun _ => True

/-- The always-false heap proposition. -/
def hfalse : HProp := fun _ => False

/-- Compatibility bridge: run a legacy flat-heap assertion on block memory via the
block-0 projection in `memBlock0ToHeap`. -/
def onMem (P : HProp) : MemHProp := fun m => P (memBlock0ToHeap m)

@[simp] theorem onMem_toMem (P : HProp) (h : Heap) :
    P.onMem (heapToMem h) ↔ P h := by
  simp [onMem]

-- Notation
infixl:35 " ∗ " => sep
infixr:25 " -∗ " => wand
notation "⌜" p "⌝" => pure p
notation "∃ₕ " => hexists
notation "∀ₕ " => hforall

end HProp
end HeytingLean.LeanCP
