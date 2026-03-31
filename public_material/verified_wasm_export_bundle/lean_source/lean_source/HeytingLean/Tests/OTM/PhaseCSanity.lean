import HeytingLean.OTM.TuringSubsumption

namespace HeytingLean.Tests.OTM

open HeytingLean.OTM
open HeytingLean.MirandaDynamics.Computation

universe u

variable {Cfg : Type u} [Inhabited Cfg] [Nontrivial Cfg]

example (c : Cfg) :
    otm_decode_cfg (Cfg := Cfg) (otm_encode_cfg c) = c :=
  otm_decode_cfg_encode (Cfg := Cfg) c

example (TM : HaltSys Cfg) (c : Cfg) :
    otm_decode_cfg (Cfg := Cfg) ((otm_of_tm (Cfg := Cfg) TM c).step.runtime.control) = TM.step c :=
  otm_step_simulates_tm_step (Cfg := Cfg) TM c

example (TM : HaltSys Cfg) (fuel : Nat) (c : Cfg) :
    otm_decode_cfg (Cfg := Cfg) ((Machine.run fuel (otm_of_tm (Cfg := Cfg) TM c)).runtime.control)
      = TM.stepN fuel c :=
  otm_run_simulates_tm_run (Cfg := Cfg) TM fuel c

example (TM : HaltSys Cfg) (c : Cfg) :
    ∃ otm : Machine Unit (Set Cfg),
      otm_decode_cfg (Cfg := Cfg) otm.runtime.control = c ∧
      ∀ fuel,
        otm_decode_cfg (Cfg := Cfg) ((Machine.run fuel otm).runtime.control) = TM.stepN fuel c :=
  turing_subsumption (Cfg := Cfg) TM c

end HeytingLean.Tests.OTM
