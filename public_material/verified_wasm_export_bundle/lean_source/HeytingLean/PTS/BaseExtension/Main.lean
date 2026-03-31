import HeytingLean.PTS.BaseExtension.Soundness
import HeytingLean.PTS.BaseExtension.Completeness
import HeytingLean.PTS.BaseExtension.ProgramSupport
import HeytingLean.PTS.BaseExtension.Contextual.Main

namespace HeytingLean.PTS.BaseExtension

theorem atom_support_iff_search (B : Base) (a : Atom) :
    Supports B (.atom a) ↔ SearchSupports (encodeBase B) (encode (.atom a)) := by
  constructor
  · exact atom_support_implies_search B a
  · exact atom_search_implies_support B a

theorem bot_support_iff_search (B : Base) :
    Supports B .bot ↔ SearchSupports (encodeBase B) (encode .bot) := by
  constructor
  · exact bot_support_implies_search B
  · exact bot_search_implies_support B

theorem atomImp_support_iff_search (B : Base) (p q : Atom) :
    Supports B (.imp (.atom p) (.atom q)) ↔
      SearchSupports (encodeBase B) (encode (.imp (.atom p) (.atom q))) := by
  constructor
  · exact atomImp_support_implies_search B p q
  · exact atomImp_search_implies_support B p q

theorem proves_iff_searchSupports (P : Program) (g : Goal) :
    Proves P g ↔ SearchSupports P g := by
  constructor
  · intro h
    exact search_complete h
  · rintro ⟨fuel, hfuel⟩
    exact search_sound hfuel

def supportSearchStatus : String :=
  "support=search status: the repo proves the atom/base bridge, bottom, the atomic implication fragment, selected executable regressions, the program-level atom bridge, and the full operational Proves↔search equivalence; the unrestricted arbitrary-program semantic bridge is refuted by the compiled absurd-clause counterexample, and the first-order contextual theorem candidate is blocked by a bare conjunction counterexample (`B = [p,q]`, `φ = p ∧ q` has semantic support while the executable search still returns false at fuel 24); the parallel contextual goal-valued subsystem adds positive executable witness probes, but this branch does not prove the paper's full Support↔Search theorem"

def contextualSupportSearchStatus : String :=
  Contextual.supportSearchStatus

example : Supports [⟨0⟩] (.atom ⟨0⟩) := by
  simp [Supports]

example : SearchSupports (encodeBase [⟨0⟩]) (encode (.atom ⟨0⟩)) := by
  exact atom_support_implies_search [⟨0⟩] ⟨0⟩ (by simp [Supports])

example : ¬ SearchSupports (encodeBase [⟨0⟩]) (encode .bot) := by
  simpa [bot_support_iff_search] using (show ¬ Supports [⟨0⟩] .bot by simp [Supports])

example : SearchSupports (encodeBase []) (encode (.imp (.atom ⟨0⟩) (.atom ⟨0⟩))) := by
  exact (atomImp_support_iff_search [] ⟨0⟩ ⟨0⟩).1 (by
    exact (supports_atom_imp_atom_iff [] ⟨0⟩ ⟨0⟩).2 (Or.inl rfl))

example : Proves [] (encode (identityFormula ⟨0⟩)) := by
  exact (proves_iff_searchSupports [] (encode (identityFormula ⟨0⟩))).2 ⟨5, by native_decide⟩

example : SearchSupports [] (encode (identityFormula ⟨0⟩)) := by
  exact ⟨5, by native_decide⟩

example : SearchSupports [] (encode (.imp (.conj (.atom ⟨0⟩) (.atom ⟨1⟩)) (.atom ⟨0⟩))) := by
  exact ⟨12, by native_decide⟩

example : search 12 [] (encode (.imp (.atom ⟨0⟩) (.disj (.atom ⟨0⟩) (.atom ⟨1⟩)))) = false := by
  native_decide

example : SearchSupports [] (encode (.imp (.conj (.imp (.atom ⟨0⟩) (.atom ⟨1⟩)) (.atom ⟨0⟩)) (.atom ⟨1⟩))) := by
  exact ⟨12, by native_decide⟩

example : SearchSupports [] (encode (.imp .bot (.atom ⟨0⟩))) := by
  exact ⟨12, by native_decide⟩

example : search 7 [] (encode (peirceFormula ⟨0⟩ ⟨1⟩)) = false := by
  native_decide

example : Supports [⟨0⟩, ⟨1⟩] (.conj (.atom ⟨0⟩) (.atom ⟨1⟩)) := by
  simp [Supports]

example : search 24 (encodeBase [⟨0⟩, ⟨1⟩]) (encode (.conj (.atom ⟨0⟩) (.atom ⟨1⟩))) = false := by
  native_decide

example : ProgramSupports [] (.atom ⟨0⟩) ↔ SearchSupports [] (encode (.atom ⟨0⟩)) := by
  exact programAtom_support_iff_search [] ⟨0⟩

example : ¬ ProgramSupports [Definite.absurd] .bot := by
  exact not_programSupports_absurd_program_bot

example : SearchSupports [Definite.absurd] (encode .bot) := by
  exact searchSupports_absurd_program_bot

example :
    ¬ (∀ B : Program, ∀ φ : IPL, ProgramSupports B φ ↔ SearchSupports B (encode φ)) := by
  exact no_global_programSupports_bridge

example :
    Contextual.OperationalSupports Contextual.basePQ (.conj (.atom ⟨0⟩) (.atom ⟨1⟩)) := by
  exact ⟨16, by native_decide⟩

end HeytingLean.PTS.BaseExtension
