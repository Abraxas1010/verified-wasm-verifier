import HeytingLean.OTM.TuringSubsumption
import HeytingLean.PerspectivalPlenum.Lens.Profile

namespace HeytingLean
namespace OTM

open HeytingLean.MirandaDynamics.Computation

/--
Profile-indexed halting horizon. Lower-dimensional profiles are intentionally
resource-bounded; higher-dimensional profiles can inspect longer traces.
-/
def horizonOfProfile (P : PerspectivalPlenum.Lens.LensProfile) : Nat :=
  if P.dimension ≤ 2 then 1 else 3

/-- OTM-side halting observation at a fixed fuel budget. -/
def otmHaltsAtFuel
    {Cfg : Type} [Inhabited Cfg] [Nontrivial Cfg]
    (TM : HaltSys Cfg) (init : Cfg) (fuel : Nat) : Prop :=
  TM.halts (otm_decode_cfg (Cfg := Cfg)
    ((Machine.run fuel (otm_of_tm (Cfg := Cfg) TM init)).runtime.control))

/-- A profile sees halting if it can witness a halting fuel within its horizon. -/
def profileHaltsBy
    {Cfg : Type} [Inhabited Cfg] [Nontrivial Cfg]
    (P : PerspectivalPlenum.Lens.LensProfile)
    (TM : HaltSys Cfg) (init : Cfg) : Prop :=
  ∃ fuel, fuel ≤ horizonOfProfile P ∧ otmHaltsAtFuel TM init fuel

/-- OTM fuel-halting view is exactly TM halting on `stepN`. -/
theorem otmHaltsAtFuel_iff_tm
    {Cfg : Type} [Inhabited Cfg] [Nontrivial Cfg]
    (TM : HaltSys Cfg) (init : Cfg) (fuel : Nat) :
    otmHaltsAtFuel TM init fuel ↔ TM.halts (TM.stepN fuel init) := by
  unfold otmHaltsAtFuel
  simp [otm_run_simulates_tm_run (Cfg := Cfg) TM fuel init]

/-- Witness TM used for the perspectival-halting lane: halt exactly at control value `2`. -/
def counterTM : HaltSys Nat where
  step := Nat.succ
  halts := fun n => n = 2

theorem counterTM_stepN_eq_add (fuel start : Nat) :
    counterTM.stepN fuel start = start + fuel := by
  induction fuel generalizing start with
  | zero =>
    simp [HaltSys.stepN]
  | succ fuel ih =>
      calc
        counterTM.stepN (Nat.succ fuel) start
            = counterTM.stepN fuel (Nat.succ start) := by
                simp [HaltSys.stepN, counterTM]
        _ = Nat.succ start + fuel := ih (Nat.succ start)
        _ = start + Nat.succ fuel := by
              simp [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm]

theorem counterTM_otmHaltsAtFuel_iff (fuel : Nat) :
    otmHaltsAtFuel counterTM 0 fuel ↔ fuel = 2 := by
  have hstep : counterTM.stepN fuel 0 = fuel := by
    simpa [Nat.zero_add] using counterTM_stepN_eq_add fuel 0
  calc
    otmHaltsAtFuel counterTM 0 fuel
        ↔ counterTM.halts (counterTM.stepN fuel 0) := otmHaltsAtFuel_iff_tm counterTM 0 fuel
    _ ↔ counterTM.stepN fuel 0 = 2 := by
      rfl
    _ ↔ fuel = 2 := by
      simp [hstep]

/-- Dimension-2 profile: bounded horizon too small to witness the step-2 halt. -/
def dim2Profile : PerspectivalPlenum.Lens.LensProfile :=
  { name := "OTM-D2"
    contradictionPolicy := PerspectivalPlenum.Lens.ContradictionPolicy.constructive
    dimension := 2
    languageTag := "otm-constructive"
    metricTag := "bounded" }

/-- Dimension-3 profile: horizon large enough to witness the step-2 halt. -/
def dim3Profile : PerspectivalPlenum.Lens.LensProfile :=
  { name := "OTM-D3"
    contradictionPolicy := PerspectivalPlenum.Lens.ContradictionPolicy.paraconsistent
    dimension := 3
    languageTag := "otm-perspectival"
    metricTag := "expanded" }

theorem dim2Profile_no_halt_for_counterTM :
    ¬ profileHaltsBy dim2Profile counterTM 0 := by
  intro h
  rcases h with ⟨fuel, hFuel, hHalts⟩
  have hEq2 : fuel = 2 := (counterTM_otmHaltsAtFuel_iff fuel).1 hHalts
  have hFuel' : fuel ≤ 1 := by
    simpa [dim2Profile, horizonOfProfile] using hFuel
  have : (2 : Nat) ≤ 1 := by
    rw [← hEq2]
    exact hFuel'
  exact (by decide : ¬ ((2 : Nat) ≤ 1)) this

theorem dim3Profile_halts_for_counterTM :
    profileHaltsBy dim3Profile counterTM 0 := by
  refine ⟨2, ?_, ?_⟩
  · simp [dim3Profile, horizonOfProfile]
  · exact (counterTM_otmHaltsAtFuel_iff 2).2 rfl

/--
Phase-E (P3) witness theorem:
the same OTM-simulated computation is non-halting in the dimension-2 profile
and halting in the dimension-3 profile.
-/
theorem otm_perspectival_halting_witness :
    ¬ profileHaltsBy dim2Profile counterTM 0 ∧
      profileHaltsBy dim3Profile counterTM 0 := by
  exact ⟨dim2Profile_no_halt_for_counterTM, dim3Profile_halts_for_counterTM⟩

/-- Existential packaging of the lens-relative halting witness. -/
theorem halting_is_perspectival :
    ∃ P₂ P₃ : PerspectivalPlenum.Lens.LensProfile,
      P₂.dimension = 2 ∧ P₃.dimension = 3 ∧
      ¬ profileHaltsBy P₂ counterTM 0 ∧ profileHaltsBy P₃ counterTM 0 := by
  refine ⟨dim2Profile, dim3Profile, rfl, rfl, ?_⟩
  exact otm_perspectival_halting_witness

end OTM
end HeytingLean
