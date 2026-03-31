import HeytingLean.OTM.Assembly
import HeytingLean.LoF.Instances
import HeytingLean.MirandaDynamics.Computation.TuringMachine

namespace HeytingLean
namespace OTM

open HeytingLean.MirandaDynamics.Computation
open scoped Classical

universe u

variable {Cfg : Type u}

/-- Encode a classical TM configuration into the OTM carrier. -/
def otm_encode_cfg (c : Cfg) : Set Cfg := {c}

/-- Decode an OTM carrier value back into a classical TM configuration. -/
noncomputable def otm_decode_cfg [Inhabited Cfg] (S : Set Cfg) : Cfg :=
  if h : S.Nonempty then Classical.choose h else default

@[simp] theorem otm_decode_cfg_encode [Inhabited Cfg] (c : Cfg) :
    otm_decode_cfg (Cfg := Cfg) (otm_encode_cfg c) = c := by
  classical
  unfold otm_decode_cfg otm_encode_cfg
  let h : ({c} : Set Cfg).Nonempty := ⟨c, by simp⟩
  simp [h]

noncomputable def otm_counter_cfg [Inhabited Cfg] [Nontrivial Cfg] : Cfg :=
  Classical.choose (exists_ne (default : Cfg))

theorem otm_counter_cfg_ne_default [Inhabited Cfg] [Nontrivial Cfg] :
    otm_counter_cfg (Cfg := Cfg) ≠ default :=
  Classical.choose_spec (exists_ne (default : Cfg))

noncomputable def tm_id_nucleus : Nucleus (Set Cfg) where
  toFun := id
  map_inf' := by
    intro A B
    rfl
  idempotent' := by
    intro A
    rfl
  le_apply' := by
    intro A
    rfl

noncomputable def tm_id_core_nucleus : Core.Nucleus (Set Cfg) where
  R := id
  extensive := by
    intro A
    exact le_rfl
  idempotent := by
    intro A
    rfl
  meet_preserving := by
    intro A B
    rfl

noncomputable def tm_support_reentry [Inhabited Cfg] [Nontrivial Cfg] :
    LoF.Reentry (Set Cfg) := by
  let c0 : Cfg := default
  let c1 : Cfg := otm_counter_cfg (Cfg := Cfg)
  have hc1 : c1 ≠ c0 := by
    simpa [c0, c1] using (otm_counter_cfg_ne_default (Cfg := Cfg))
  refine
    { nucleus := tm_id_nucleus (Cfg := Cfg)
      primordial := ({c0} : Set Cfg)
      counter := ({c1} : Set Cfg)
      support := ({c0} : Set Cfg)
      primordial_mem := rfl
      counter_mem := rfl
      primordial_nonbot := by
        refine bot_lt_iff_ne_bot.mpr ?_
        intro h
        have hmem : c0 ∈ ({c0} : Set Cfg) := by simp
        have : c0 ∈ (⊥ : Set Cfg) := by
          rw [← h]
          exact hmem
        exact False.elim this
      counter_nonbot := by
        refine bot_lt_iff_ne_bot.mpr ?_
        intro h
        have hmem : c1 ∈ ({c1} : Set Cfg) := by simp
        have : c1 ∈ (⊥ : Set Cfg) := by
          rw [← h]
          exact hmem
        exact False.elim this
      orthogonal := by
        ext x
        constructor
        · intro hx
          rcases hx with ⟨hx0, hx1⟩
          have hx0' : x = c0 := by simpa using hx0
          have hx1' : x = c1 := by simpa using hx1
          exact (hc1 (hx1'.symm.trans hx0')).elim
        · intro hx
          exact False.elim hx
      primordial_in_support := by
        exact le_rfl
      map_bot := rfl
      primordial_minimal := by
        intro x _hxFix hxPos hxSupport y hy
        have hxNe : x ≠ (⊥ : Set Cfg) := bot_lt_iff_ne_bot.mp hxPos
        have hxNonempty : x.Nonempty := Set.nonempty_iff_ne_empty.mpr (by simpa using hxNe)
        rcases hxNonempty with ⟨w, hw⟩
        have hw0 : w = c0 := by
          have hwInSupport : w ∈ ({c0} : Set Cfg) := hxSupport hw
          simpa using hwInSupport
        have h0in : c0 ∈ x := by
          simpa [hw0] using hw
        have hy0 : y = c0 := by
          simpa using hy
        simpa [hy0] using h0in }

noncomputable def tm_id_ratchet_step : RatchetStepCore (Set Cfg) where
  step := id
  extensive := by
    intro J
    exact le_rfl
  monotone := by
    intro J K hJK
    exact hJK
  idempotent := by
    intro J
    rfl

noncomputable def tm_ratchet_interface : RatchetInterface (Set Cfg) :=
  RatchetInterface.ofStep
    (step := tm_id_ratchet_step (Cfg := Cfg))
    (level := fun n => n)
    (htraj := by
      intro fuel₁ fuel₂ h
      exact h)

noncomputable def tm_tape [Inhabited Cfg] [Nontrivial Cfg] :
    Tape Unit (Set Cfg) (tm_id_core_nucleus (Cfg := Cfg)) where
  cells := fun _ => (⊥ : Set Cfg)
  fixed := by
    intro _
    rfl

/-- Control-state update used by the TM→OTM simulation wrapper. -/
def tm_control_step [Inhabited Cfg] (TM : HaltSys Cfg) (σ : Set Cfg) : Set Cfg :=
  otm_encode_cfg (TM.step (otm_decode_cfg (Cfg := Cfg) σ))

/-- Transition kernel used by `otm_of_tm`. -/
def tm_transition [Inhabited Cfg] (TM : HaltSys Cfg) :
    Set Cfg → Set Cfg → TransitionPacket (Set Cfg)
  | σ, _ =>
      { nextState := tm_control_step (Cfg := Cfg) TM σ
        move := HeadMove.stay
        writeVal := (⊥ : Set Cfg) }

/-- Canonical OTM instance used to simulate a classical deterministic TM system. -/
noncomputable def otm_of_tm [Inhabited Cfg] [Nontrivial Cfg]
    (TM : HaltSys Cfg) (init : Cfg) : Machine Unit (Set Cfg) where
  nucleus := { core := tm_id_core_nucleus (Cfg := Cfg) }
  reentry := { core := tm_support_reentry (Cfg := Cfg) }
  ratchet := tm_ratchet_interface (Cfg := Cfg)
  nucleus_reentry_compat := by
    intro x
    rfl
  tape := tm_tape (Cfg := Cfg)
  runtime :=
    { head := ()
      control := otm_encode_cfg init }
  advanceHead := fun _ _ => ()
  transition := tm_transition (Cfg := Cfg) TM
  transition_fixed := by
    intro σ c
    rfl

/-- One OTM step decodes to one TM step on control state. -/
theorem otm_step_simulates_tm_step [Inhabited Cfg] [Nontrivial Cfg]
    (TM : HaltSys Cfg) (c : Cfg) :
    otm_decode_cfg (Cfg := Cfg) ((otm_of_tm (Cfg := Cfg) TM c).step.runtime.control) = TM.step c := by
  simp [Machine.step, Machine.readCurrent, otm_of_tm, tm_transition, tm_control_step]

theorem run_control_eq_iter [Inhabited Cfg] [Nontrivial Cfg]
    (TM : HaltSys Cfg) (M : Machine Unit (Set Cfg))
    (htr : M.transition = tm_transition (Cfg := Cfg) TM) :
    ∀ fuel,
      (Machine.run fuel M).runtime.control
        = Nat.iterate (tm_control_step (Cfg := Cfg) TM) fuel M.runtime.control
  | 0 => rfl
  | Nat.succ fuel => by
      have htrStep : (M.step).transition = tm_transition (Cfg := Cfg) TM := by
        simpa [Machine.step] using htr
      calc
        (Machine.run (Nat.succ fuel) M).runtime.control
            = (Machine.run fuel (M.step)).runtime.control := rfl
        _ = Nat.iterate (tm_control_step (Cfg := Cfg) TM) fuel (M.step).runtime.control :=
            run_control_eq_iter TM (M := M.step) htrStep fuel
        _ = Nat.iterate (tm_control_step (Cfg := Cfg) TM) fuel
              (tm_control_step (Cfg := Cfg) TM M.runtime.control) := by
            simp [Machine.step, Machine.readCurrent, htr, tm_transition, tm_control_step]
        _ = Nat.iterate (tm_control_step (Cfg := Cfg) TM) (Nat.succ fuel) M.runtime.control := by
            simp [Nat.iterate]

theorem decode_iter_tm_control_step [Inhabited Cfg] (TM : HaltSys Cfg) :
    ∀ fuel σ,
      otm_decode_cfg (Cfg := Cfg) (Nat.iterate (tm_control_step (Cfg := Cfg) TM) fuel σ)
        = TM.stepN fuel (otm_decode_cfg (Cfg := Cfg) σ)
  | 0, σ => by
      simp
  | Nat.succ fuel, σ => by
      simp [Nat.iterate, tm_control_step,
        decode_iter_tm_control_step (TM := TM) fuel]

/-- Fuel-bounded OTM execution decodes to TM `stepN` execution. -/
theorem otm_run_simulates_tm_run [Inhabited Cfg] [Nontrivial Cfg]
    (TM : HaltSys Cfg) (fuel : Nat) (c : Cfg) :
    otm_decode_cfg (Cfg := Cfg) ((Machine.run fuel (otm_of_tm (Cfg := Cfg) TM c)).runtime.control)
      = TM.stepN fuel c := by
  have hrun :
      (Machine.run fuel (otm_of_tm (Cfg := Cfg) TM c)).runtime.control
        = Nat.iterate (tm_control_step (Cfg := Cfg) TM) fuel (otm_encode_cfg c) := by
    simpa [otm_of_tm] using
      run_control_eq_iter (Cfg := Cfg) TM (M := otm_of_tm (Cfg := Cfg) TM c) rfl fuel
  rw [hrun]
  simpa [otm_decode_cfg_encode] using
    decode_iter_tm_control_step (Cfg := Cfg) (TM := TM) fuel (otm_encode_cfg c)

/--
Conservative subsumption theorem:
for any classical deterministic TM system and initial configuration, there exists an OTM instance
whose decoded control trace matches the TM execution trace.
-/
theorem turing_subsumption [Inhabited Cfg] [Nontrivial Cfg]
    (TM : HaltSys Cfg) (c : Cfg) :
    ∃ otm : Machine Unit (Set Cfg),
      otm_decode_cfg (Cfg := Cfg) otm.runtime.control = c ∧
      ∀ fuel,
        otm_decode_cfg (Cfg := Cfg) ((Machine.run fuel otm).runtime.control) = TM.stepN fuel c := by
  refine ⟨otm_of_tm (Cfg := Cfg) TM c, ?_, ?_⟩
  · simp [otm_of_tm]
  · intro fuel
    simpa using (otm_run_simulates_tm_run (Cfg := Cfg) TM fuel c)

end OTM
end HeytingLean
