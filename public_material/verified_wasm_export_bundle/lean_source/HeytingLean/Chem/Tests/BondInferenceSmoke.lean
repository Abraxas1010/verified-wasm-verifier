import HeytingLean.Chem.Bonding.Inference
import HeytingLean.Chem.PeriodicTable.Elements
import Mathlib.Tactic

namespace HeytingLean
namespace Chem
namespace Tests

open HeytingLean.Chem.Bonding
open HeytingLean.Chem.PeriodicTable
open HeytingLean.Chem.PeriodicTable.Elements

def waterAtoms : Fin 3 → Atom
  | ⟨0, _⟩ => { element := O }
  | ⟨1, _⟩ => { element := H }
  | ⟨2, _⟩ => { element := H }

def methaneAtoms : Fin 5 → Atom
  | ⟨0, _⟩ => { element := C }
  | _ => { element := H }

example : (inferBondGraph? waterAtoms 2 1).map (fun g => g.bonds.card) = some 2 := by
  native_decide

example : (inferBondGraph? methaneAtoms 4 1).map (fun g => g.bonds.card) = some 4 := by
  native_decide

-- Spot-check the central-atom valence degree in the inferred graphs.
example : (inferBondGraph? waterAtoms 2 1).map (fun g => BondGraph.valenceDegree g ⟨0, by decide⟩) = some 2 := by
  native_decide

example : (inferBondGraph? methaneAtoms 4 1).map (fun g => BondGraph.valenceDegree g ⟨0, by decide⟩) = some 4 := by
  native_decide

-- Structural invariant: inferred graphs are loop-free.
example (g : BondGraph 3) (hg : g ∈ inferBondGraphs waterAtoms 2 1) : BondGraph.Valid g :=
  inferBondGraphs_valid (atoms := waterAtoms) (maxEdges := 2) (maxOrder := 1) g hg

end Tests
end Chem
end HeytingLean
