import HeytingLean.Genesis.CantorWitness
import HeytingLean.Genesis.Glossary
import HeytingLean.Genesis.Stabilization

/-!
# Genesis.Observer

Phase-2 observer layer:
- Observer v1 alias (depth, choices, phase)
- completed observers as Cantor paths
- compatibility and canonical completion
-/

namespace HeytingLean.Genesis

/-- Phase-2 observer v1 (kept identical to glossary contract). -/
abbrev Observer : Type := ObserverV1

def completedObserver_equiv_evalPath : CompletedObserver ≃ EvalPath := Equiv.refl _

/-- A completed observer extends a finite observer when it matches all finite choices. -/
def compatible (o : Observer) (p : CompletedObserver) : Prop :=
  ∀ i : Fin o.depth, p i = o.choices i

/-- Canonical total completion of a finite observer by filling beyond depth with `false`. -/
def defaultCompletion (o : Observer) : CompletedObserver :=
  fun n => if h : n < o.depth then o.choices ⟨n, h⟩ else false

theorem defaultCompletion_compatible (o : Observer) : compatible o (defaultCompletion o) := by
  intro i
  simp [defaultCompletion, i.is_lt]

theorem exists_completion (o : Observer) : ∃ p : CompletedObserver, compatible o p :=
  ⟨defaultCompletion o, defaultCompletion_compatible o⟩

/-- Phase process induced at time `n` for a completed observer. -/
def phaseAt (p : CompletedObserver) (n : Nat) : Iterant Bool :=
  phaseSequence p n

@[simp] theorem phaseAt_eq (p : CompletedObserver) (n : Nat) :
    phaseAt p n = evalLife (p n) := rfl

theorem completedObserver_card : Cardinal.mk CompletedObserver = Cardinal.continuum := by
  change Cardinal.mk EvalPath = Cardinal.continuum
  exact evalPath_card

/-! ## Tier-1 claim-surface theorem (LEP T1.8) -/

/-- Support extracted from a finite observer via its canonical completion. -/
def observerSupport (o : Observer) : Support :=
  { n : Nat | defaultCompletion o n = true }

/-- Eigenform representative for an observer: closure under the stabilization nucleus. -/
def observerEigenSupport (o : Observer) : Support :=
  collapseNucleus (observerSupport o)

/-- Observer-as-eigenform: the observer-induced support is a fixed point of `R`. -/
theorem observer_as_eigenform (o : Observer) :
    collapseNucleus (observerEigenSupport o) = observerEigenSupport o := by
  simp [observerEigenSupport]

end HeytingLean.Genesis
