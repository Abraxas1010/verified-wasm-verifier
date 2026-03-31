import HeytingLean.Certified.Program
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Int.Order.Basic
import Mathlib.Order.MinMax

namespace HeytingLean
namespace Certified
namespace Thermo

open Certified

private def v0_1_0 : SemVer := { major := 0, minor := 1, patch := 0 }

def energyScale3 : Nat → Nat :=
  fun t => 3 * t

def energyClamp0_30000 : Nat → Nat :=
  fun e => Nat.min 30000 e

private theorem energyScale3_monotone :
    Property.Holds .monotone .nat .nat energyScale3 := by
  intro a b hab
  exact Nat.mul_le_mul_left 3 hab

def progEnergyScale3 : CertifiedProgram :=
  let props : List Property := [.monotone]
  CertifiedProgram.mkHashed
    (id := "thermo_energy_scale3")
    (name := "thermo_energy_scale3")
    (version := v0_1_0)
    (dom := .nat) (cod := .nat)
    (dimension := .D1_Heyting)
    (lenses := [.core, .c])
    (properties := props) (invariants := [])
    (fn := energyScale3)
    (propProofs := by
      intro p hp
      have hp' : p = .monotone := by
        simpa [props] using (List.mem_singleton.mp hp)
      subst hp'
      simpa using energyScale3_monotone)
    (cCode :=
      "/* thermo_energy_scale3: Nat -> Nat */\n" ++
      "#include <stdint.h>\n" ++
      "uint32_t thermo_energy_scale3(uint32_t t) {\n" ++
      "  return 3u * t;\n" ++
      "}\n")

private theorem energyClamp0_30000_bounded :
    Property.Holds (.boundedNat 0 30000) .nat .nat energyClamp0_30000 := by
  intro e
  constructor
  · exact Nat.zero_le _
  · exact Nat.min_le_left _ _

private theorem energyClamp0_30000_monotone :
    Property.Holds .monotone .nat .nat energyClamp0_30000 := by
  intro a b hab
  exact min_le_min_left 30000 hab

def progEnergyClamp0_30000 : CertifiedProgram :=
  let props : List Property := [.boundedNat 0 30000, .monotone]
  CertifiedProgram.mkHashed
    (id := "thermo_energy_clamp_0_30000")
    (name := "thermo_energy_clamp_0_30000")
    (version := v0_1_0)
    (dom := .nat) (cod := .nat)
    (dimension := .D1_Heyting)
    (lenses := [.core, .c])
    (properties := props) (invariants := [.boundedNat 0 30000])
    (fn := energyClamp0_30000)
    (propProofs := by
      intro p hp
      have hb : p = .boundedNat 0 30000 ∨ p = .monotone := by
        simpa [props] using hp
      cases hb with
      | inl hb =>
          subst hb
          simpa using energyClamp0_30000_bounded
      | inr hm =>
          subst hm
          simpa using energyClamp0_30000_monotone)
    (cCode :=
      "/* thermo_energy_clamp_0_30000: Nat -> Nat */\n" ++
      "#include <stdint.h>\n" ++
      "uint32_t thermo_energy_clamp_0_30000(uint32_t e) {\n" ++
      "  if (e > 30000u) return 30000u;\n" ++
      "  return e;\n" ++
      "}\n")

def energyId : Nat → Nat := fun e => e

private theorem energyId_conservative :
    Property.Holds .conservative .nat .nat energyId := by
  intro e
  rfl

private theorem energyId_monotone :
    Property.Holds .monotone .nat .nat energyId := by
  intro a b hab
  simpa using hab

def progEnergyId : CertifiedProgram :=
  let props : List Property := [.conservative, .monotone]
  CertifiedProgram.mkHashed
    (id := "thermo_energy_id")
    (name := "thermo_energy_id")
    (version := v0_1_0)
    (dom := .nat) (cod := .nat)
    (dimension := .D1_Heyting)
    (lenses := [.core, .c])
    (properties := props) (invariants := [])
    (fn := energyId)
    (propProofs := by
      intro p hp
      have hc : p = .conservative ∨ p = .monotone := by
        simpa [props] using hp
      cases hc with
      | inl hc =>
          subst hc
          simpa using energyId_conservative
      | inr hm =>
          subst hm
          simpa using energyId_monotone)
    (cCode :=
      "/* thermo_energy_id: Nat -> Nat */\n" ++
      "#include <stdint.h>\n" ++
      "uint32_t thermo_energy_id(uint32_t e) {\n" ++
      "  return e;\n" ++
      "}\n")

def energyLose1 : Nat → Nat := fun e => Nat.pred e

private theorem energyLose1_monotone :
    Property.Holds .monotone .nat .nat energyLose1 := by
  intro a b hab
  exact Nat.pred_le_pred hab

def progEnergyLose1 : CertifiedProgram :=
  let props : List Property := [.monotone]
  CertifiedProgram.mkHashed
    (id := "thermo_energy_lose1")
    (name := "thermo_energy_lose1")
    (version := v0_1_0)
    (dom := .nat) (cod := .nat)
    (dimension := .D1_Heyting)
    (lenses := [.core, .c])
    (properties := props) (invariants := [])
    (fn := energyLose1)
    (propProofs := by
      intro p hp
      have hp' : p = .monotone := by
        simpa [props] using (List.mem_singleton.mp hp)
      subst hp'
      simpa using energyLose1_monotone)
    (cCode :=
      "/* thermo_energy_lose1: Nat -> Nat */\n" ++
      "#include <stdint.h>\n" ++
      "uint32_t thermo_energy_lose1(uint32_t e) {\n" ++
      "  if (e == 0u) return 0u;\n" ++
      "  return e - 1u;\n" ++
      "}\n")

def deltaTFromTemp300 : Nat → Int :=
  fun t => (Int.ofNat t) - 300

private theorem deltaTFromTemp300_monotone :
    Property.Holds .monotone .nat .int deltaTFromTemp300 := by
  intro a b hab
  have h' : (Int.ofNat a) ≤ (Int.ofNat b) := Int.ofNat_le_ofNat_of_le hab
  exact sub_le_sub_right h' 300

def progDeltaTFromTemp300 : CertifiedProgram :=
  let props : List Property := [.monotone]
  CertifiedProgram.mkHashed
    (id := "thermo_deltaT_from_temp300")
    (name := "thermo_deltaT_from_temp300")
    (version := v0_1_0)
    (dom := .nat) (cod := .int)
    (dimension := .D1_Heyting)
    (lenses := [.core, .c])
    (properties := props) (invariants := [])
    (fn := deltaTFromTemp300)
    (propProofs := by
      intro p hp
      have hp' : p = .monotone := by
        simpa [props] using (List.mem_singleton.mp hp)
      subst hp'
      simpa using deltaTFromTemp300_monotone)
    (cCode :=
      "/* thermo_deltaT_from_temp300: Nat -> Int\n" ++
      "   Convention: output is signed (can be negative).\n" ++
      "*/\n" ++
      "#include <stdint.h>\n" ++
      "int32_t thermo_deltaT_from_temp300(uint32_t t) {\n" ++
      "  return (int32_t)t - 300;\n" ++
      "}\n")

def sigmaSquare : Int → Int := fun x => x * x

private theorem sigmaSquare_nonneg :
    Property.Holds .nonnegInt .int .int sigmaSquare := by
  intro x
  simpa [sigmaSquare] using (mul_self_nonneg x)

def progSigmaSquare : CertifiedProgram :=
  let props : List Property := [.nonnegInt]
  CertifiedProgram.mkHashed
    (id := "thermo_sigma_square")
    (name := "thermo_sigma_square")
    (version := v0_1_0)
    (dom := .int) (cod := .int)
    (dimension := .D1_Heyting)
    (lenses := [.core, .c])
    (properties := props) (invariants := [.nonnegInt])
    (fn := sigmaSquare)
    (propProofs := by
      intro p hp
      have hp' : p = .nonnegInt := by
        simpa [props] using (List.mem_singleton.mp hp)
      subst hp'
      simpa using sigmaSquare_nonneg)
    (cCode :=
      "/* thermo_sigma_square: Int -> Int */\n" ++
      "#include <stdint.h>\n" ++
      "int32_t thermo_sigma_square(int32_t x) {\n" ++
      "  return x * x;\n" ++
      "}\n")

def sigmaLinear : Int → Int := fun x => x

private theorem sigmaLinear_conservative :
    Property.Holds .conservative .int .int sigmaLinear := by
  intro x
  rfl

private theorem sigmaLinear_monotone :
    Property.Holds .monotone .int .int sigmaLinear := by
  intro a b hab
  simpa using hab

def progSigmaLinear : CertifiedProgram :=
  let props : List Property := [.conservative, .monotone]
  CertifiedProgram.mkHashed
    (id := "thermo_sigma_linear")
    (name := "thermo_sigma_linear")
    (version := v0_1_0)
    (dom := .int) (cod := .int)
    (dimension := .D1_Heyting)
    (lenses := [.core, .c])
    (properties := props) (invariants := [])
    (fn := sigmaLinear)
    (propProofs := by
      intro p hp
      have hc : p = .conservative ∨ p = .monotone := by
        simpa [props] using hp
      cases hc with
      | inl hc =>
          subst hc
          simpa using sigmaLinear_conservative
      | inr hm =>
          subst hm
          simpa using sigmaLinear_monotone)
    (cCode :=
      "/* thermo_sigma_linear: Int -> Int (not nonnegative on all inputs) */\n" ++
      "#include <stdint.h>\n" ++
      "int32_t thermo_sigma_linear(int32_t x) {\n" ++
      "  return x;\n" ++
      "}\n")

def libraryPrograms : List CertifiedProgram :=
  [ progEnergyScale3
  , progEnergyClamp0_30000
  , progEnergyId
  , progEnergyLose1
  , progDeltaTFromTemp300
  , progSigmaSquare
  , progSigmaLinear
  ]

end Thermo
end Certified
end HeytingLean
