import HeytingLean.Chem.Interactions.Analytic.Bonded
import HeytingLean.Chem.PeriodicTable.Elements

/-!
# Bonded-energy smoke tests (analytic layer)
-/

namespace HeytingLean
namespace Chem
namespace Tests

open HeytingLean.Chem
open HeytingLean.Chem.Bonding
open HeytingLean.Chem.Interactions.Analytic
open HeytingLean.Chem.PeriodicTable.Elements

noncomputable section

example : True := by
  let e : BondEdge 2 :=
    ⟨⟨0, by decide⟩, ⟨1, by decide⟩, { kind := .covalent, order := some .single }⟩
  let g : BondGraph 2 :=
    { atoms := fun _ => { element := H, charge := 0 }
      bonds := { e } }
  let cfg : Configuration 2 :=
    { atoms := fun _ => { element := H, charge := 0 }
      pos := fun
        | ⟨0, _⟩ => fun _ => 0
        | ⟨1, _⟩ => fun _ => 0 }
  let p : HarmonicBondParams := { k := 0, r0 := 0 }
  have : totalBondStretchEnergy g cfg (fun _ => p) = 0 := by
    simp [totalBondStretchEnergy, harmonicBondEnergy, g, cfg, p, e]
  trivial

end

end Tests
end Chem
end HeytingLean
