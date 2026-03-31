import HeytingLean.OTM.DynamicsComputation.ReverseCorrespondence

/-!
# OTM.Reverse

Compatibility re-export for legacy reverse-correspondence path.
-/

namespace HeytingLean.OTM.Reverse

open HeytingLean.OTM.DynamicsComputation

abbrev UniversalClosedEvaluator (X : Type _) :=
  HeytingLean.OTM.DynamicsComputation.UniversalClosedEvaluator X

abbrev TMEncoding (Cfg : Type _) (X : Type _) :=
  HeytingLean.OTM.DynamicsComputation.TMEncoding Cfg X

theorem nucleus_universal_implies_partial_recursive_simulation
    {X : Type _}
    (J : Nucleus (Set X))
    (E : UniversalClosedEvaluator X) :
    ∀ f : Set X → Set X, ∃ c : E.Code, E.eval c = f :=
  DynamicsComputation.nucleus_universal_implies_partial_recursive_simulation J E

theorem nucleus_universal_implies_composition_simulation
    {X : Type _}
    (J : Nucleus (Set X))
    (E : UniversalClosedEvaluator X) :
    ∀ f g : Set X → Set X, ∃ c : E.Code, E.eval c = g ∘ f :=
  DynamicsComputation.nucleus_universal_implies_composition_simulation J E

theorem decode_iter_step_code_eq_stepN
    {X : Type _} {Cfg : Type _}
    (E : UniversalClosedEvaluator X)
    (Enc : TMEncoding Cfg X)
    (TM : HeytingLean.MirandaDynamics.Computation.HaltSys Cfg)
    {code : E.Code}
    (hcode : E.eval code = (fun s => Enc.encode (TM.step (Enc.decode s)))) :
    ∀ fuel cfg,
      Enc.decode (Nat.iterate (E.eval code) fuel (Enc.encode cfg)) = TM.stepN fuel cfg :=
  DynamicsComputation.decode_iter_step_code_eq_stepN E Enc TM hcode

theorem nucleus_universal_implies_tm_simulation
    {X : Type _} {Cfg : Type _}
    (J : Nucleus (Set X))
    (E : UniversalClosedEvaluator X)
    (Enc : TMEncoding Cfg X)
    (TM : HeytingLean.MirandaDynamics.Computation.HaltSys Cfg) :
    ∃ code : E.Code,
      ∀ fuel cfg,
        Enc.decode (Nat.iterate (E.eval code) fuel (Enc.encode cfg)) = TM.stepN fuel cfg :=
  DynamicsComputation.nucleus_universal_implies_tm_simulation J E Enc TM

end HeytingLean.OTM.Reverse
