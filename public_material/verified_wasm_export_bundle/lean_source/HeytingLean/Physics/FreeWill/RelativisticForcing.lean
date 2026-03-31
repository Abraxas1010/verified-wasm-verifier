import Mathlib
import HeytingLean.Physics.FreeWill.Relativity

set_option autoImplicit false

namespace HeytingLean.Physics.FreeWill

/--
`UnmarkedFuture past out` means two worlds share the same accessible past,
while differing on outcome.
-/
def UnmarkedFuture {World : Type*} {Past : Type*} {Outcome : Type*}
    (past : World → Past) (out : World → Outcome) : Prop :=
  ∃ w1 w2 : World, past w1 = past w2 ∧ out w1 ≠ out w2

/--
`Predictable past out` means there is a function on past-information fibers
that reproduces the outcome exactly.
-/
def Predictable {World : Type*} {Past : Type*} {Outcome : Type*}
    (past : World → Past) (out : World → Outcome) : Prop :=
  ∃ predict : Set.range past → Outcome,
    ∀ w : World, predict ⟨past w, ⟨w, rfl⟩⟩ = out w

/-- If there is no disagreement at equal-past worlds, a predictor exists. -/
theorem predictable_of_not_unmarkedFuture
    {World : Type*} {Past : Type*} {Outcome : Type*}
    (past : World → Past) (out : World → Outcome)
    (h : ¬ UnmarkedFuture past out) :
    Predictable past out := by
  classical
  let pick : Set.range past → World := fun p => Classical.choose p.2
  have pick_spec : ∀ p : Set.range past, past (pick p) = p.1 := by
    intro p
    exact Classical.choose_spec p.2
  refine ⟨fun p => out (pick p), ?_⟩
  intro w
  have hsame : past (pick ⟨past w, ⟨w, rfl⟩⟩) = past w := by
    simpa using pick_spec ⟨past w, ⟨w, rfl⟩⟩
  by_cases hEq : out (pick ⟨past w, ⟨w, rfl⟩⟩) = out w
  · exact hEq
  · exact False.elim (h ⟨pick ⟨past w, ⟨w, rfl⟩⟩, w, hsame, hEq⟩)

/-- Contrapositive form used in the Free-Will endpoint. -/
theorem unmarkedFuture_of_not_predictable
    {World : Type*} {Past : Type*} {Outcome : Type*}
    (past : World → Past) (out : World → Outcome)
    (h : ¬ Predictable past out) :
    UnmarkedFuture past out := by
  by_cases hUF : UnmarkedFuture past out
  · exact hUF
  · exact False.elim (h (predictable_of_not_unmarkedFuture past out hUF))

/--
Accessibility-indexed form of `UnmarkedFuture`:
two events share accessible information while differing in outcome.
-/
def UnmarkedFutureAccessible
    {Event Fact Outcome : Type*}
    (I : AccessibleInfo Event Fact)
    (out : Event → Outcome) : Prop :=
  ∃ e₁ e₂ : Event, SameAccessibleInfo I e₁ e₂ ∧ out e₁ ≠ out e₂

/--
Bridge from projection-style unmarked future (`past`) to accessibility-style
unmarked future (`AccessibleInfo`), given a compatibility law.
-/
theorem unmarkedFuture_accessible_of_projection
    {Event Fact Past Outcome : Type*}
    (I : AccessibleInfo Event Fact)
    (past : Event → Past)
    (out : Event → Outcome)
    (hCompat : ∀ e₁ e₂, SameAccessibleInfo I e₁ e₂ ↔ past e₁ = past e₂)
    (hUF : UnmarkedFuture past out) :
    UnmarkedFutureAccessible I out := by
  rcases hUF with ⟨e₁, e₂, hPast, hOut⟩
  exact ⟨e₁, e₂, (hCompat e₁ e₂).2 hPast, hOut⟩

/--
Accessibility-indexed unmarked-future endpoint derived from non-predictability
plus compatibility between accessible-information equivalence and `past`.
-/
theorem unmarkedFuture_accessible_of_not_predictable
    {Event Fact Past Outcome : Type*}
    (I : AccessibleInfo Event Fact)
    (past : Event → Past)
    (out : Event → Outcome)
    (hCompat : ∀ e₁ e₂, SameAccessibleInfo I e₁ e₂ ↔ past e₁ = past e₂)
    (hNotPred : ¬ Predictable past out) :
    UnmarkedFutureAccessible I out := by
  exact unmarkedFuture_accessible_of_projection I past out hCompat
    (unmarkedFuture_of_not_predictable past out hNotPred)

end HeytingLean.Physics.FreeWill
