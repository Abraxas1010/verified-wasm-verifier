import Mathlib.Computability.Halting
import Mathlib.Computability.PartrecCode

namespace HeytingLean
namespace InqBQ

open Encodable
open Nat.Partrec
open Nat.Partrec.Code

/-- Coq-style Boolean reflection. -/
def CoqReflects (b : Bool) (p : Prop) : Prop :=
  p ↔ b = true

/-- Coq-style Boolean decider. -/
def CoqDecider {α : Type*} (f : α → Bool) (p : α → Prop) : Prop :=
  ∀ x, CoqReflects (f x) (p x)

/-- Coq-style decidability witness. -/
def CoqDecidable {α : Type*} (p : α → Prop) : Prop :=
  ∃ f : α → Bool, CoqDecider f p

/-- Coq Trakhtenbrot-style recursive enumeration witness. -/
def CoqRecEnum {α : Type*} (p : α → Prop) : Prop :=
  ∃ Q : Nat → α → Bool, ∀ x, p x ↔ ∃ n, Q n x = true

theorem coqDecidable_of_decidablePred {α : Type*} {p : α → Prop} [DecidablePred p] :
    CoqDecidable p := by
  refine ⟨fun x => decide (p x), ?_⟩
  intro x
  exact (Bool.decide_iff (p x)).symm

/-- Any Mathlib r.e. predicate yields a Coq-style recursive enumeration witness. -/
theorem coqRecEnum_of_rePred
    {α : Type*} [Primcodable α] {p : α → Prop} (hp : REPred p) :
    CoqRecEnum p := by
  let f : α →. Unit := fun a => Part.assert (p a) fun _ => Part.some ()
  have hf : Partrec f := hp
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 ((Partrec.bind_decode₂_iff (f := f)).1 hf)
  refine ⟨fun n a => (Nat.Partrec.Code.evaln n c (encode a)).isSome, ?_⟩
  intro a
  have hca : Nat.Partrec.Code.eval c (encode a) = (f a).map encode := by
    simpa [f, decode₂_encode] using congrArg (fun g => g (encode a)) hc
  constructor
  · intro ha
    have hDomf : (f a).Dom := by
      dsimp [f]
      simp [Part.assert_pos ha]
    have hDomEval : (Nat.Partrec.Code.eval c (encode a)).Dom := by
      simpa [hca] using hDomf
    rcases Part.dom_iff_mem.mp hDomEval with ⟨y, hy⟩
    rcases (Nat.Partrec.Code.evaln_complete).1 hy with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rcases hEvaln : Nat.Partrec.Code.evaln n c (encode a) with _ | z
    · simp [hEvaln] at hn
    · simp [hEvaln]
  · rintro ⟨n, hn⟩
    rcases hEvaln : Nat.Partrec.Code.evaln n c (encode a) with _ | y
    · simp [hEvaln] at hn
    · have hy : y ∈ Nat.Partrec.Code.evaln n c (encode a) := by
        simp [hEvaln]
      have hMemEval : y ∈ Nat.Partrec.Code.eval c (encode a) :=
        (Nat.Partrec.Code.evaln_complete).2 ⟨n, hy⟩
      have hDomEval : (Nat.Partrec.Code.eval c (encode a)).Dom :=
        Part.dom_iff_mem.mpr ⟨y, hMemEval⟩
      have hDomf : (f a).Dom := by
        simpa [hca] using hDomEval
      by_cases hpa : p a
      · exact hpa
      · have : ¬ (f a).Dom := by
          dsimp [f]
          simp [Part.assert_neg hpa]
        exact False.elim (this hDomf)

end InqBQ
end HeytingLean
