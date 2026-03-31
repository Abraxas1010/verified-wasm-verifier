import HeytingLean.PTS.BaseExtension.Contextual.Support

namespace HeytingLean.PTS.BaseExtension.Contextual

def supportSearchStatus : String :=
  "contextual support=search status: the parent program-base generalization project is complete as a misformalized closeout. Program-level Base, V4 semantics, general search_cut, conjunction forward, and implication backward are landed; the blanket implication-forward bridge shape is retired by bounded/kernel evidence; the stronger global head-search packaging for conjunction backward is also retired; and the narrower conjunction-only follow-on was retired as misformalized once the residual callbacks were recognized as arbitrary Goal-level obligations outside the current formula-level Supports semantics. The remaining real theorem work is isolated to support_search_v4_goal_support_generalization_20260325. scripts/support_search_phase3_gate.sh remains the mandatory pre-flight gate for conjunction follow-on work."

def basePQ : Base :=
  baseOfAtoms [⟨0⟩, ⟨1⟩]

example : OperationalSupports basePQ (.conj (.atom ⟨0⟩) (.atom ⟨1⟩)) := by
  exact ⟨16, by native_decide⟩

example :
    SearchSupports (encodeBase basePQ) (encode (.conj (.atom ⟨0⟩) (.atom ⟨1⟩))) := by
  exact ⟨16, by native_decide⟩

example :
    SupportsCtx [(.conj (.atom ⟨0⟩) (.atom ⟨1⟩))] (baseOfAtoms [])
      (.atom ⟨0⟩) := by
  exact ⟨16, by native_decide⟩

example :
    SearchSupports (encodeBase (baseOfAtoms []))
      (encode (.imp (.conj (.atom ⟨0⟩) (.atom ⟨1⟩)) (.atom ⟨0⟩))) := by
  exact ⟨16, by native_decide⟩

example :
    SearchSupports (encodeBase (baseOfAtoms []))
      (encode (.imp (.atom ⟨0⟩) (.disj (.atom ⟨0⟩) (.atom ⟨1⟩)))) := by
  exact ⟨16, by native_decide⟩

example :
    search 8 (encodeBase (baseOfAtoms [])) (encode (peirceFormula ⟨0⟩ ⟨1⟩)) = false := by
  native_decide

end Contextual
end HeytingLean.PTS.BaseExtension
