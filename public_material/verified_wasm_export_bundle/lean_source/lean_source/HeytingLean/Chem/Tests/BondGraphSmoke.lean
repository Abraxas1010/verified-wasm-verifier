import HeytingLean.Chem.Bonding.BondGraph
import HeytingLean.Chem.PeriodicTable.Elements

namespace HeytingLean.Chem.Tests

open HeytingLean.Chem
open HeytingLean.Chem.Bonding
open HeytingLean.Chem.PeriodicTable.Elements

def hAtom : Atom := { element := H, charge := 0 }
def oAtom : Atom := { element := O, charge := 0 }

def waterGraph : BondGraph 2 :=
  { atoms :=
      fun
        | ⟨0, _⟩ => hAtom
        | ⟨1, _⟩ => oAtom
    bonds := { ⟨⟨0, by decide⟩, ⟨1, by decide⟩, { kind := .covalent, order := some .single }⟩ }
  }

example : BondGraph.Valid waterGraph := by
  intro e he
  -- The only bond is between indices 0 and 1.
  have : e = ⟨⟨0, by decide⟩, ⟨1, by decide⟩, { kind := .covalent, order := some .single }⟩ := by
    simpa [waterGraph] using (Finset.mem_singleton.mp he)
  simp [this]

end HeytingLean.Chem.Tests

