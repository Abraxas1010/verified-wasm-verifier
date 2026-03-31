import HeytingLean.OTM.PerspectivalHalting
import HeytingLean.OTM.TransfiniteIndex

namespace HeytingLean
namespace OTM

/-- Canonical initial state for the counter-style integration example. -/
def counterInit : Nat := 0

/-- Binary-counter style execution: decoded control equals the fuel count. -/
theorem counter_example_decode_run (fuel : Nat) :
    otm_decode_cfg (Cfg := Nat)
        ((Machine.run fuel (otm_of_tm (Cfg := Nat) counterTM counterInit)).runtime.control) = fuel := by
  calc
    otm_decode_cfg (Cfg := Nat)
        ((Machine.run fuel (otm_of_tm (Cfg := Nat) counterTM counterInit)).runtime.control)
        = counterTM.stepN fuel counterInit := by
            simpa using otm_run_simulates_tm_run (Cfg := Nat) counterTM fuel counterInit
    _ = fuel := by
      simpa [counterInit, Nat.zero_add] using counterTM_stepN_eq_add fuel counterInit

theorem counter_example_halts_at_two :
    otmHaltsAtFuel counterTM counterInit 2 := by
  exact (counterTM_otmHaltsAtFuel_iff 2).2 rfl

theorem counter_example_not_halts_at_one :
    ¬ otmHaltsAtFuel counterTM counterInit 1 := by
  intro h
  have hEq : (1 : Nat) = 2 := (counterTM_otmHaltsAtFuel_iff 1).1 h
  exact (by decide : (1 : Nat) ≠ 2) hEq

/-- Surreal-index micro-example: `ω` has birthday index `ω`. -/
theorem surreal_index_micro_example :
    preGameIndex Numbers.Surreal.TransfinitePreGame.PreGame.omega =
      Numbers.Ordinal.OrdinalCNF.omega :=
  preGameIndex_omega

/--
Phase-G (P7) integration witness:
counter-style OTM execution and surreal birthday indexing co-exist in the same
certified OTM scaffold.
-/
theorem otm_integration_examples_witness :
    (∀ fuel,
      otm_decode_cfg (Cfg := Nat)
          ((Machine.run fuel (otm_of_tm (Cfg := Nat) counterTM counterInit)).runtime.control)
            = fuel) ∧
      otmHaltsAtFuel counterTM counterInit 2 ∧
      ¬ otmHaltsAtFuel counterTM counterInit 1 ∧
      preGameIndex Numbers.Surreal.TransfinitePreGame.PreGame.omega =
        Numbers.Ordinal.OrdinalCNF.omega := by
  refine ⟨counter_example_decode_run, counter_example_halts_at_two, ?_, surreal_index_micro_example⟩
  exact counter_example_not_halts_at_one

end OTM
end HeytingLean
