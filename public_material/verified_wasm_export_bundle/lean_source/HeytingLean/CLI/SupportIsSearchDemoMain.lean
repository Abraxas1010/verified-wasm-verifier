import HeytingLean.PTS.BaseExtension.Modes
import HeytingLean.PTS.BaseExtension.Contextual.Main
import HeytingLean.ATP.Ensemble.ConstructivityCheck

namespace HeytingLean.CLI

open PTS.BaseExtension
open ATP.Ensemble

def renderCase (label : String) (value : Bool) : String :=
  s!"{label}: {(if value then "true" else "false")}"

def SupportIsSearchDemo.run : IO UInt32 := do
  let idOk := searchWithMode .intuitionistic 5 [] (identityFormula ⟨0⟩)
  let peirceOk := searchWithMode .intuitionistic 7 [] (peirceFormula ⟨0⟩ ⟨1⟩)
  let hornIdOk := searchWithMode .classicalHorn 5 [] (identityFormula ⟨0⟩)
  let contextualConjBase :=
    Contextual.search 16 (Contextual.encodeBase (Contextual.baseOfAtoms [⟨0⟩, ⟨1⟩]))
      (Contextual.encode (.conj (.atom ⟨0⟩) (.atom ⟨1⟩)))
  let contextualConjElim :=
    Contextual.search 16 (Contextual.encodeBase (Contextual.baseOfAtoms []))
      (Contextual.encode (.imp (.conj (.atom ⟨0⟩) (.atom ⟨1⟩)) (.atom ⟨0⟩)))
  IO.println (renderCase "identity" idOk)
  IO.println (renderCase "peirce" peirceOk)
  IO.println (renderCase "classical_horn_identity" hornIdOk)
  IO.println (renderCase "contextual_conj_base" contextualConjBase)
  IO.println (renderCase "contextual_conj_elim" contextualConjElim)
  IO.println (renderCase "constructive_gate" rejectsPeirce)
  IO.println (renderCase "double_negation_gate" rejectsDoubleNegationElim)
  pure 0

end HeytingLean.CLI

def main (args : List String) : IO UInt32 :=
  let _ := args
  HeytingLean.CLI.SupportIsSearchDemo.run
