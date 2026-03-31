import HeytingLean.LeanCP.Core.HProp
import HeytingLean.LeanCP.Lang.CSemantics

/-!
# LeanCP State-Sensitive Propositions

State-sensitive propositions (`SProp`) are predicates over the full LeanCP
machine state. They extend the heap-only `HProp` surface without replacing it.
-/

namespace HeytingLean.LeanCP

/-- State-sensitive assertions over the full machine state. -/
def SProp := CState → Prop

namespace SProp

/-- Empty-state heap assertion. -/
def emp : SProp := fun st => st.heap = Heap.empty

/-- Singleton heap cell assertion over the current state. -/
def pointsTo (addr : Nat) (v : CVal) : SProp :=
  fun st => st.heap = Heap.write Heap.empty addr v

/-- Separating conjunction over states: split only the heap, share env/allocator state. -/
def sep (P Q : SProp) : SProp := fun st =>
  ∃ h1 h2, Finmap.Disjoint h1 h2 ∧
    st.heap = Heap.union h1 h2 ∧
    P { st with heap := h1 } ∧
    Q { st with heap := h2 }

/-- Magic wand over states: extend only the heap, keep env/allocator state fixed. -/
def wand (P Q : SProp) : SProp := fun st =>
  ∀ h', Finmap.Disjoint st.heap h' →
    P { st with heap := h' } →
    Q { st with heap := Heap.union st.heap h' }

/-- Pure proposition, requiring an empty heap. -/
def pure (p : Prop) : SProp := fun st => st.heap = Heap.empty ∧ p

/-- Heap-agnostic proposition over the current state. -/
def fact (p : Prop) : SProp := fun _ => p

/-- Existential quantification over state-sensitive assertions. -/
def sexists {α : Type} (P : α → SProp) : SProp := fun st => ∃ a, P a st

/-- Universal quantification over state-sensitive assertions. -/
def sforall {α : Type} (P : α → SProp) : SProp := fun st => ∀ a, P a st

/-- Disjunction over the same state. -/
def hor (P Q : SProp) : SProp := fun st => P st ∨ Q st

/-- Conjunction over the same state. -/
def hand (P Q : SProp) : SProp := fun st => P st ∧ Q st

/-- Always true. -/
def strue : SProp := fun _ => True

/-- Always false. -/
def sfalse : SProp := fun _ => False

/-- Assert that a variable lookup returns a specific value. -/
def hasVar (x : String) (v : CVal) : SProp := fun st => st.lookupVar x = some v

/-- Lift a heap-only assertion to the current machine state. -/
def ofHProp (P : HProp) : SProp := fun st => P st.heap

/-- Lift a block-memory assertion to the current machine state by embedding the
legacy flat heap into block memory. -/
def ofMemHProp (P : MemHProp) : SProp := fun st => P (heapToMem st.heap)

@[simp] theorem ofHProp_eq_ofMemHProp_onMem (P : HProp) :
    ofHProp P = ofMemHProp P.onMem := by
  funext st
  simp [ofHProp, ofMemHProp]

infixl:35 " ∗ₛ " => sep
infixr:25 " -∗ₛ " => wand

end SProp
end HeytingLean.LeanCP
