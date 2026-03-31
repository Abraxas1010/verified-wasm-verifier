import HeytingLean.OTM.TuringSubsumption
import HeytingLean.MirandaDynamics.Discrete.HaltingToPeriodic
import HeytingLean.OTM.DynamicsComputation.NucleusFromDynamics

namespace HeytingLean
namespace OTM
namespace DynamicsComputation

open HeytingLean.MirandaDynamics.Computation
open HeytingLean.MirandaDynamics.Discrete

universe u

variable {Cfg : Type u}

/--
Forward milestone: the classical TM lane already yields a concrete computational nucleus.
Here the witness is the identity nucleus used in `OTM.TuringSubsumption`.
-/
theorem tm_complete_implies_has_nucleus :
    ∀ [Inhabited Cfg], ∃ J : Nucleus (Set Cfg), ∀ U : Set Cfg, J U = U := by
  intro _inst
  refine ⟨tm_id_nucleus (Cfg := Cfg), ?_⟩
  intro U
  rfl

/--
Forward trace correspondence exported from the OTM subsumption lane.
-/
theorem forward_trace_correspondence
    [Inhabited Cfg] [Nontrivial Cfg] (TM : HaltSys Cfg) (init : Cfg) :
    ∃ otm : Machine Unit (Set Cfg),
      otm_decode_cfg (Cfg := Cfg) otm.runtime.control = init ∧
      ∀ fuel,
        otm_decode_cfg (Cfg := Cfg) ((Machine.run fuel otm).runtime.control) = TM.stepN fuel init :=
  turing_subsumption (Cfg := Cfg) TM init

/--
Halting vs. stabilization equivalence in the discrete dynamics reduction lane.
This is the formalized "halting <-> reaches periodic orbit" bridge.
-/
theorem halting_stabilization_iff_fixedpoint (n : Nat) (c : Nat.Partrec.Code) :
    ReachesPeriod2 n c ↔ HeytingLean.MirandaDynamics.Undecidability.Halting.Halts n c :=
  reachesPeriod2_iff_halts n c

/--
Forward undecidability transfer package: halting many-one reduces to reaching period-2.
-/
def halting_reduces_to_period2 (n : Nat) :
    HeytingLean.MirandaDynamics.Undecidability.ManyOne
      (p := HeytingLean.MirandaDynamics.Undecidability.Halting.Halts n)
      (q := fun c : Nat.Partrec.Code => ReachesPeriod2 n c) :=
  haltingReducesToReachesPeriod2 n

/--
Forward undecidability consequence: the period-2 reachability predicate is not computable.
-/
theorem periodic_orbit_predicate_not_computable (n : Nat) :
    ¬ComputablePred (fun c : Nat.Partrec.Code => ReachesPeriod2 n c) :=
  not_computable_reachesPeriod2 n

end DynamicsComputation
end OTM
end HeytingLean
