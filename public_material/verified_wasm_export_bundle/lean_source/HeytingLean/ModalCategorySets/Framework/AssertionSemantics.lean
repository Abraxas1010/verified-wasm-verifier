import HeytingLean.ModalCategorySets.Framework.KripkeCategory

namespace HeytingLean.ModalCategorySets.Framework

universe u v

/-- Abstract assertion semantics over a Kripke category. This is the theorem-1 core
without committing to a specific first-order syntax. -/
structure AssertionSemantics (Obj : Type u) where
  C : KripkeCategory Obj
  Assertion : Type v
  holds : Obj → Assertion → Prop
  possible : Assertion → Assertion
  necessary : Assertion → Assertion
  holds_possible_iff :
    ∀ X a, holds X (possible a) ↔ ∃ Y, C.toFrame.rel X Y ∧ holds Y a
  holds_necessary_iff :
    ∀ X a, holds X (necessary a) ↔ ∀ Y, C.toFrame.rel X Y → holds Y a

namespace AssertionSemantics

variable {Obj : Type u} (S : AssertionSemantics Obj)

/-- Accessibility preserves and reflects truth of every assertion. -/
def TruthInvariant : Prop :=
  ∀ {X Y}, S.C.toFrame.rel X Y → ∀ a, S.holds X a ↔ S.holds Y a

/-- Possibility collapses to actuality everywhere. -/
def PossibleTrivializes : Prop :=
  ∀ X a, S.holds X (S.possible a) ↔ S.holds X a

/-- Necessity collapses to actuality everywhere. -/
def NecessaryTrivializes : Prop :=
  ∀ X a, S.holds X (S.necessary a) ↔ S.holds X a

theorem truthInvariant_implies_possibleTrivializes
    (hInv : S.TruthInvariant) :
    S.PossibleTrivializes := by
  intro X a
  constructor
  · intro hPoss
    rcases (S.holds_possible_iff X a).1 hPoss with ⟨Y, hXY, hYa⟩
    exact (hInv hXY a).2 hYa
  · intro hXa
    exact (S.holds_possible_iff X a).2
      (Exists.intro X (And.intro (KripkeCategory.frame_reflexive (C := S.C) X) hXa))

theorem truthInvariant_implies_necessaryTrivializes
    (hInv : S.TruthInvariant) :
    S.NecessaryTrivializes := by
  intro X a
  constructor
  · intro hNec
    exact (S.holds_necessary_iff X a).1 hNec X
      (KripkeCategory.frame_reflexive (C := S.C) X)
  · intro hXa
    exact (S.holds_necessary_iff X a).2 (by
      intro Y hXY
      exact (hInv hXY a).1 hXa)

theorem trivializes_implies_truthInvariant
    (hPoss : S.PossibleTrivializes)
    (hNec : S.NecessaryTrivializes) :
    S.TruthInvariant := by
  intro X Y hXY a
  constructor
  · intro hXa
    have hNecessary : S.holds X (S.necessary a) := (hNec X a).2 hXa
    exact (S.holds_necessary_iff X a).1 hNecessary Y hXY
  · intro hYa
    have hPossible : S.holds X (S.possible a) :=
      (S.holds_possible_iff X a).2 (Exists.intro Y (And.intro hXY hYa))
    exact (hPoss X a).1 hPossible

theorem truthInvariant_iff_modalitiesTrivialize :
    S.TruthInvariant ↔ S.PossibleTrivializes ∧ S.NecessaryTrivializes := by
  constructor
  · intro hInv
    exact And.intro
      (S.truthInvariant_implies_possibleTrivializes hInv)
      (S.truthInvariant_implies_necessaryTrivializes hInv)
  · intro h
    exact S.trivializes_implies_truthInvariant h.1 h.2

end AssertionSemantics

end HeytingLean.ModalCategorySets.Framework
