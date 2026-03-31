import HeytingLean.LoF.Bauer.LawvereFixedPoint
import HeytingLean.OTM.DynamicsComputation.NucleusFromDynamics
import HeytingLean.MirandaDynamics.Computation.TuringMachine

namespace HeytingLean
namespace OTM
namespace DynamicsComputation

open HeytingLean.LoF.Bauer
open HeytingLean.MirandaDynamics.Computation

universe u v w

variable {X : Type u}

/--
Interface for the reverse-direction milestone:
closed propositions support a universal evaluator over endomaps.
-/
structure UniversalClosedEvaluator (X : Type u) where
  Code : Type v
  eval : Code → Set X → Set X
  universal : ∀ f : Set X → Set X, ∃ c : Code, eval c = f

theorem evaluator_surjective (E : UniversalClosedEvaluator X) :
    ∀ f : Set X → Set X, ∃ c : E.Code, E.eval c = f :=
  E.universal

/--
Conditional reverse milestone: if a universal evaluator is available, every endomap on
closed propositions can be represented by some code.
-/
theorem nucleus_universal_implies_partial_recursive_simulation
    (_J : Nucleus (Set X)) (E : UniversalClosedEvaluator X) :
    ∀ f : Set X → Set X, ∃ c : E.Code, E.eval c = f := by
  intro f
  exact E.universal f

/--
Encoding contract needed to interpret evaluator states as TM configurations.
-/
structure TMEncoding (Cfg : Type w) (X : Type u) where
  encode : Cfg → Set X
  decode : Set X → Cfg
  decode_encode : ∀ cfg : Cfg, decode (encode cfg) = cfg

/--
Universal evaluator yields a code for one TM-step transformer in encoded space.
-/
theorem exists_tm_step_code
    {Cfg : Type w}
    (E : UniversalClosedEvaluator X)
    (Enc : TMEncoding Cfg X)
    (TM : HaltSys Cfg) :
    ∃ code : E.Code, E.eval code = (fun s => Enc.encode (TM.step (Enc.decode s))) := by
  simpa using E.universal (fun s => Enc.encode (TM.step (Enc.decode s)))

/--
Composition witness: universal evaluators can realize composition of two
endomaps on closed propositions.
-/
theorem exists_composition_code
    (E : UniversalClosedEvaluator X)
    (f g : Set X → Set X) :
    ∃ code : E.Code, E.eval code = g ∘ f := by
  simpa using E.universal (g ∘ f)

/--
Code-level composition witness: compose two evaluator codes inside the same
universal evaluator.
-/
theorem exists_code_composing_codes
    (E : UniversalClosedEvaluator X)
    (c₁ c₂ : E.Code) :
    ∃ code : E.Code, E.eval code = E.eval c₂ ∘ E.eval c₁ := by
  simpa using E.universal (E.eval c₂ ∘ E.eval c₁)

/--
Reverse-direction composition milestone:
if a universal evaluator exists, composition closure is available in-code.
-/
theorem nucleus_universal_implies_composition_simulation
    (_J : Nucleus (Set X))
    (E : UniversalClosedEvaluator X) :
    ∀ f g : Set X → Set X, ∃ code : E.Code, E.eval code = g ∘ f := by
  intro f g
  exact exists_composition_code E f g

/--
Main reverse-direction simulation lemma (fuel-bounded):
once a step-code is chosen, decoding iterated evaluator execution matches `TM.stepN`.
-/
theorem decode_iter_step_code_eq_stepN
    {Cfg : Type w}
    (E : UniversalClosedEvaluator X)
    (Enc : TMEncoding Cfg X)
    (TM : HaltSys Cfg)
    {code : E.Code}
    (hcode : E.eval code = (fun s => Enc.encode (TM.step (Enc.decode s)))) :
    ∀ fuel cfg,
      Enc.decode (Nat.iterate (E.eval code) fuel (Enc.encode cfg)) = TM.stepN fuel cfg
  | 0, cfg => by
      simp [Enc.decode_encode]
  | Nat.succ fuel, cfg => by
      calc
        Enc.decode (Nat.iterate (E.eval code) (Nat.succ fuel) (Enc.encode cfg))
            = Enc.decode (Nat.iterate (E.eval code) fuel ((E.eval code) (Enc.encode cfg))) := by
                simp [Nat.iterate]
        _ = Enc.decode (Nat.iterate (E.eval code) fuel (Enc.encode (TM.step cfg))) := by
              simp [hcode, Enc.decode_encode]
        _ = TM.stepN fuel (TM.step cfg) := decode_iter_step_code_eq_stepN E Enc TM hcode fuel (TM.step cfg)
        _ = TM.stepN (Nat.succ fuel) cfg := by
              simp [HaltSys.stepN]

/--
Reverse correspondence milestone (strengthened):
from universal evaluator and an encoding, obtain an explicit evaluator code that simulates
`stepN` under decode for all fuel bounds.
-/
theorem nucleus_universal_implies_tm_simulation
    {Cfg : Type w}
    (_J : Nucleus (Set X))
    (E : UniversalClosedEvaluator X)
    (Enc : TMEncoding Cfg X)
    (TM : HaltSys Cfg) :
    ∃ code : E.Code,
      ∀ fuel cfg,
        Enc.decode (Nat.iterate (E.eval code) fuel (Enc.encode cfg)) = TM.stepN fuel cfg := by
  rcases exists_tm_step_code E Enc TM with ⟨code, hcode⟩
  refine ⟨code, ?_⟩
  intro fuel cfg
  exact decode_iter_step_code_eq_stepN E Enc TM hcode fuel cfg

/--
Lawvere fixed-point transfer helper used by reverse-direction proofs.
-/
theorem lawvere_fixedpoint_of_pointSurjective
    {A : Type u} {B : Type v}
    (e : A → A → B) (he : Lawvere.PointSurjective e) (f : B → B) :
    ∃ b : B, f b = b :=
  Lawvere.exists_fixedPoint_of_pointSurjective e he f

end DynamicsComputation
end OTM
end HeytingLean
