import HeytingLean.Genesis
import Mathlib.SetTheory.Cardinal.Continuum

/-!
# Genesis Phase 2 Sanity
-/

namespace HeytingLean.Tests.Genesis

open HeytingLean.Genesis
open Cardinal

#check EvalPath
#check EvalPathFrom
#check eval_tree_self_similar
#check evalPath_card
#check EmergentRegion
#check regionOfRep
#check infRepRegion
#check supRepRegion
#check inf_well_defined
#check sup_well_defined
#check regionInf
#check regionSup
#check inf_comm
#check inf_assoc
#check inf_idem
#check sup_comm
#check sup_assoc
#check sup_idem
#check absorption_inf_sup
#check Observer
#check CompletedObserver
#check completedObserver_equiv_evalPath

def obs0 : Observer where
  depth := 0
  choices := fun i => nomatch i
  phase := phaseI

example : #(EvalPath) = Cardinal.continuum := evalPath_card

example : ∃ p : CompletedObserver, compatible obs0 p := exists_completion obs0

example (pre : List Bool) : #(EvalPathFrom pre) = Cardinal.continuum :=
  evalPathFrom_card pre

example : regionInf (regionOfRep CoGame.Life) (regionOfRep CoGame.Life) = regionOfRep CoGame.Life := by
  simp [regionInf, regionOfRep]

example :
    regionSup (regionOfRep CoGame.Void) (regionOfRep CoGame.Life) =
      regionSup (regionOfRep CoGame.Life) (regionOfRep CoGame.Void) := by
  simpa using Genesis.sup_comm (regionOfRep CoGame.Void) (regionOfRep CoGame.Life)

end HeytingLean.Tests.Genesis
