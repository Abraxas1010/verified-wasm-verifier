import HeytingLean.Bridges.Nucleus.NucleusRegistry
import HeytingLean.LoF.Bauer.DoubleNegation
import HeytingLean.Eigen.NucleusReLU
import HeytingLean.MirandaDynamics.FixedPoint.PeriodicNucleus

namespace HeytingLean
namespace Tests
namespace Bridges
namespace NucleusSanity

open Set
open HeytingLean.Bridges.Nucleus

/-! Conversion surface smoke checks (D1). -/
#check coreToMathlib
#check mathlibToCore
#check heytingToMathlib
#check mathlibToHeyting
#check ruleToMathlib
#check mathlibToRule
#check calculusToMathlib
#check mathlibToCalculus

section RoundtripChecks

variable {L : Type*} [SemilatticeInf L] [OrderBot L]
variable {α : Type*} [HeytingAlgebra α]
variable {β : Type*} [CompleteLattice β]

example (N : HeytingLean.Core.Nucleus L) :
    mathlibToCore (coreToMathlib N) = N :=
  mathlibToCore_coreToMathlib N

example (N : HeytingLean.Core.Heyting.Nucleus α) :
    mathlibToHeyting (heytingToMathlib N) = N :=
  mathlibToHeyting_heytingToMathlib N

example (N : HeytingLean.Calculus.RuleNucleus) :
    mathlibToRule (ruleToMathlib N) = N :=
  mathlibToRule_ruleToMathlib N

example (N : HeytingLean.Calculus.CalculusNucleus β) :
    mathlibToCalculus (calculusToMathlib N) = N :=
  mathlibToCalculus_calculusToMathlib N

end RoundtripChecks

/-! Sheaf glue smoke checks (D3): definition-level + interior + bundles. -/
#check thm_sheaf_glue_nucleus_core_to_nucleus_mathlib
#check thm_sheaf_glue_nucleus_mathlib_to_nucleus_core
#check thm_sheaf_glue_nucleus_core_to_nucleus_heyting
#check thm_sheaf_glue_nucleus_heyting_to_nucleus_core
#check thm_sheaf_glue_nucleus_mathlib_to_nucleus_rule
#check thm_sheaf_glue_nucleus_rule_to_nucleus_mathlib
#check thm_sheaf_glue_nucleus_heyting_to_nucleus_calculus
#check thm_sheaf_glue_nucleus_calculus_to_nucleus_heyting
#check thm_sheaf_glue_nucleus_rule_to_nucleus_calculus
#check thm_sheaf_glue_nucleus_calculus_to_nucleus_rule

#check qgiToInt
#check intToQgiWithSupport
#check qgiToInt_intToQgiWithSupport
#check intToQgiWithSupport_qgiToInt
#check thm_sheaf_glue_nucleus_qgi_to_nucleus_int
#check thm_sheaf_glue_nucleus_int_to_nucleus_qgi_with_support

#check reentryToMathlib
#check ctToMathlib
#check worldToMathlib
#check thm_sheaf_glue_nucleus_reentry_to_nucleus_mathlib
#check thm_sheaf_glue_nucleus_ct_to_nucleus_mathlib
#check thm_sheaf_glue_nucleus_world_to_nucleus_mathlib

/-! Registry sanity (D4). -/
example : allNucleusTags.length = 36 := by
  decide

#eval allNucleusTags.length

/-! Concrete nucleus instance smoke checks (D5). -/
#check (HeytingLean.LoF.Bauer.doubleNegNucleus Bool : _root_.Nucleus Bool)
#check (HeytingLean.Eigen.reluNucleus 3 : _root_.Nucleus (Fin 3 → ℝ))
#check (HeytingLean.MirandaDynamics.FixedPoint.unionNucleus (α := Nat) (∅ : Set Nat) :
  _root_.Nucleus (Set Nat))

example :
    HeytingLean.Eigen.reluNucleus 3 (fun _ => (-1 : ℝ)) ⟨0, by decide⟩ = 0 := by
  simp [HeytingLean.Eigen.reluNucleus, HeytingLean.Eigen.relu]

end NucleusSanity
end Bridges
end Tests
end HeytingLean
