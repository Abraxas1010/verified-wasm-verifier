import HeytingLean.MirandaDynamics.Thermal.HardwareLedger.Basic
import HeytingLean.Chem.Bonding.Formula
import HeytingLean.Chem.PeriodicTable.Elements

/-!
# Thermal Hardware Ledger (Materials)

Phase 1 materials library for "likely compute-hardware materials".

Important:
- This is not a teardown BOM. These are *standard reference stacks* and materials that commonly
  appear in PCBs, IC packaging, VRMs, heatsinks, and TIMs.
- We represent only what we can justify with evidence/provenance in the external ledger JSON.

Proof focus:
- Provide small, stable lemmas about internal consistency (e.g. alloy mass fractions sum to 1).
- Provide reusable proof templates (interval safety bound lemmas live in `Basic.lean`).
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Thermal
namespace HardwareLedger

open HeytingLean.Chem
open HeytingLean.Chem.PeriodicTable
open HeytingLean.Chem.PeriodicTable.Elements

structure AlloyMassFractions where
  sn : Rat
  ag : Rat
  cu : Rat
  deriving Repr

namespace AlloyMassFractions

def sumsToOne (a : AlloyMassFractions) : Prop :=
  a.sn + a.ag + a.cu = 1

end AlloyMassFractions

/-- SAC305 lead-free solder: Sn96.5 Ag3.0 Cu0.5 (mass fractions). -/
def sac305 : AlloyMassFractions :=
  { sn := (965 : Rat) / 1000
    ag := (3 : Rat) / 100
    cu := (1 : Rat) / 200
  }

theorem sac305_sumsToOne : AlloyMassFractions.sumsToOne sac305 := by
  -- 0.965 + 0.03 + 0.005 = 1
  unfold AlloyMassFractions.sumsToOne sac305
  norm_num

/-- Element-tagged mass fraction record (ties hardware alloys to the periodic table). -/
structure ElementMassFraction where
  elem : PeriodicTable.Element
  frac : Rat
  deriving Repr

namespace ElementMassFraction

def sum (xs : List ElementMassFraction) : Rat :=
  xs.foldl (fun acc x => acc + x.frac) 0

end ElementMassFraction

/-- SAC305 as periodic-table tagged mass fractions (Sn/Ag/Cu). -/
def sac305_elems : List ElementMassFraction :=
  [ { elem := Sn, frac := sac305.sn }
  , { elem := Ag, frac := sac305.ag }
  , { elem := Cu, frac := sac305.cu }
  ]

theorem sac305_elems_sum_one : ElementMassFraction.sum sac305_elems = 1 := by
  -- reuse the already-proved fraction sum (syntactic fold).
  unfold ElementMassFraction.sum sac305_elems
  simp [List.foldl]
  -- Now: sac305.sn + sac305.ag + sac305.cu = 1.
  -- Expand and close by the alloy lemma.
  have h : AlloyMassFractions.sumsToOne sac305 := sac305_sumsToOne
  simpa [AlloyMassFractions.sumsToOne, sac305] using h

/-- TIM filler example: ZnO as a stoichiometric formula (1 Zn, 1 O). -/
def formula_ZnO : Chem.Formula :=
  Chem.Formula.single Zn 1 + Chem.Formula.single O 1

/-- TIM filler example: Al2O3 as a stoichiometric formula (2 Al, 3 O). -/
def formula_Al2O3 : Chem.Formula :=
  Chem.Formula.single Al 2 + Chem.Formula.single O 3

/-- MLCC dielectric example: BaTiO3 as a stoichiometric formula (1 Ba, 1 Ti, 3 O). -/
def formula_BaTiO3 : Chem.Formula :=
  Chem.Formula.single Ba 1 + Chem.Formula.single Ti 1 + Chem.Formula.single O 3

end HardwareLedger
end Thermal
end MirandaDynamics
end HeytingLean
