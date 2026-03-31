namespace HeytingLean
namespace PerspectivalPlenum
namespace Lens

/-- Policy governing how a lens treats contradictions. -/
inductive ContradictionPolicy where
  | constructive
  | booleanStrict
  | paraconsistent
  | weighted
  deriving DecidableEq, Repr

/-- Metadata and contradiction policy for a perspective lens. -/
structure LensProfile where
  name : String
  contradictionPolicy : ContradictionPolicy
  dimension : Nat := 0
  languageTag : String := ""
  metricTag : String := ""

/-- Whether the profile can allow contradictory descriptions locally. -/
def allowsContradictions (P : LensProfile) : Prop :=
  match P.contradictionPolicy with
  | .paraconsistent => True
  | .weighted => True
  | .constructive => False
  | .booleanStrict => False

@[simp] theorem allowsContradictions_paraconsistent (n l m) :
    allowsContradictions
      { name := n
        contradictionPolicy := ContradictionPolicy.paraconsistent
        dimension := l
        languageTag := m } := by
  simp [allowsContradictions]

@[simp] theorem allowsContradictions_weighted (n l m) :
    allowsContradictions
      { name := n
        contradictionPolicy := ContradictionPolicy.weighted
        dimension := l
        languageTag := m } := by
  simp [allowsContradictions]

@[simp] theorem not_allowsContradictions_constructive (n l m) :
    ¬ allowsContradictions
      { name := n
        contradictionPolicy := ContradictionPolicy.constructive
        dimension := l
        languageTag := m } := by
  simp [allowsContradictions]

@[simp] theorem not_allowsContradictions_booleanStrict (n l m) :
    ¬ allowsContradictions
      { name := n
        contradictionPolicy := ContradictionPolicy.booleanStrict
        dimension := l
        languageTag := m } := by
  simp [allowsContradictions]

end Lens
end PerspectivalPlenum
end HeytingLean
