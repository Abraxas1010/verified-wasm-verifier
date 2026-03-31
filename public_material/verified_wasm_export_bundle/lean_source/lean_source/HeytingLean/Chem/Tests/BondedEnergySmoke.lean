import HeytingLean.Chem.Interactions.Bonded

/-!
# Bonded-energy smoke tests (computable layer)
-/

namespace HeytingLean
namespace Chem
namespace Tests

open HeytingLean.Chem
open HeytingLean.Chem.Bonding
open HeytingLean.Chem.Interactions

example : True := by
  let e : BondEdge 2 :=
    ⟨⟨0, by decide⟩, ⟨1, by decide⟩, { kind := .covalent, order := some .single }⟩
  let g : BondGraph 2 :=
    { atoms := fun _ => { element := ⟨0, by decide⟩, charge := 0 }
      bonds := { e } }
  let cfg : Configuration 2 :=
    { atoms := fun _ => { element := ⟨0, by decide⟩, charge := 0 }
      dist := fun _ _ => 1 }
  let p : HarmonicBondParams := { k := 0, r0 := 1 }
  have : totalBondStretchEnergy g cfg (fun _ => p) = 0 := by
    simp [totalBondStretchEnergy, harmonicBondEnergy, g, cfg, p, e]
  trivial

end Tests
end Chem
end HeytingLean
