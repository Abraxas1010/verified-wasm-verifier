import Mathlib.Data.Rat.Defs
import HeytingLean.Chem.Foundations.Terms

/-!
# Physical constants (provenance-first; exact constants preferred)

We store constants as exact decimal-scaled rationals when possible (notably the SI-defining
constants like c, h, e, k_B, N_A). This is enough for symbolic/proof work and for bridges that
need stable identifiers and values, without committing to a full units/dimensions framework.

Source: NIST publication of CODATA 2022 recommended values (published 2025):
https://www.nist.gov/publications/codata-recommended-values-fundamental-physical-constants-2022
-/

namespace HeytingLean
namespace Chem
namespace Foundations

open HeytingLean.Chem.Foundations

/-- A very lightweight unit tag. Later we can replace this with a real dimensions/units system. -/
abbrev Unit := String

/-- A base-10 scaled rational: `mantissa * 10^exp10` (where exp10 may be negative). -/
structure ScaledDecimal where
  mantissa : Int
  exp10    : Int

namespace ScaledDecimal

/-- Convert `10^n` (for `n >= 0`) into a positive integer. -/
def pow10Nat (n : Nat) : Int :=
  (10 : Int) ^ n

/-- Convert to a rational number exactly. -/
def toRat (x : ScaledDecimal) : ℚ :=
  if x.exp10 ≥ 0 then
    let n : Nat := Int.toNat x.exp10
    Rat.divInt (x.mantissa * pow10Nat n) 1
  else
    let n : Nat := Int.toNat (-x.exp10)
    Rat.divInt x.mantissa (pow10Nat n)

end ScaledDecimal

/-- A physical constant with a stable symbol, unit label, exact value (as a rational), and provenance. -/
structure PhysicalConstant where
  name       : String
  symbol     : String
  unit       : Unit
  value      : ScaledDecimal
  provenance : Provenance

namespace PhysicalConstant

/-- Convenience: interpret the stored scaled-decimal as a rational. -/
def valueRat (c : PhysicalConstant) : ℚ :=
  c.value.toRat

end PhysicalConstant

def codata2022 : Provenance :=
  { source := "NIST: CODATA 2022 recommended values of the fundamental physical constants (published 2025)"
    url := "https://www.nist.gov/publications/codata-recommended-values-fundamental-physical-constants-2022"
    note := "Use as provenance for constant values; many SI-defining constants are exact by definition." }

/-- Speed of light in vacuum (exact by SI definition): 299792458 m/s. -/
def cLight : PhysicalConstant :=
  { name := "speed of light in vacuum"
    symbol := "c"
    unit := "m s^-1"
    value := { mantissa := 299792458, exp10 := 0 }
    provenance := codata2022 }

/-- Planck constant (exact by SI definition): 6.62607015e-34 J s. -/
def planckH : PhysicalConstant :=
  { name := "Planck constant"
    symbol := "h"
    unit := "J s"
    value := { mantissa := 662607015, exp10 := -42 }
    provenance := codata2022 }

/-- Elementary charge (exact by SI definition): 1.602176634e-19 C. -/
def elementaryCharge : PhysicalConstant :=
  { name := "elementary charge"
    symbol := "e"
    unit := "C"
    value := { mantissa := 1602176634, exp10 := -28 }
    provenance := codata2022 }

/-- Boltzmann constant (exact by SI definition): 1.380649e-23 J/K. -/
def boltzmannK : PhysicalConstant :=
  { name := "Boltzmann constant"
    symbol := "k_B"
    unit := "J K^-1"
    value := { mantissa := 1380649, exp10 := -29 }
    provenance := codata2022 }

/-- Avogadro constant (exact by SI definition): 6.02214076e23 mol^-1. -/
def avogadroNA : PhysicalConstant :=
  { name := "Avogadro constant"
    symbol := "N_A"
    unit := "mol^-1"
    value := { mantissa := 602214076, exp10 := 15 }
    provenance := codata2022 }

end Foundations
end Chem
end HeytingLean
