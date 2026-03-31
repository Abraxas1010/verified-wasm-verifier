import HeytingLean.InqBQ.NonRE
import Mathlib.Computability.Reduce

namespace HeytingLean
namespace InqBQ

open Nat.Partrec

theorem REPred.of_manyOneReducible
    {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α → Prop} {q : β → Prop}
    (hred : p ≤₀ q) (hq : REPred q) :
    REPred p := by
  rcases hred with ⟨f, hf, hcorr⟩
  have hcomp : REPred (fun a => q (f a)) := by
    simpa [REPred] using hq.comp hf
  exact REPred.of_eq (p := fun a => q (f a)) (q := p) hcomp (fun a => (hcorr a).symm)

theorem not_computable_of_manyOneReducible
    {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α → Prop} {q : β → Prop}
    (hred : p ≤₀ q) (hp : ¬ ComputablePred p) :
    ¬ ComputablePred q := by
  intro hq
  exact hp (ComputablePred.computable_of_manyOneReducible hred hq)

theorem not_re_of_not_computable_of_re_compl
    {α : Type*} [Primcodable α] {p : α → Prop}
    (hp : ¬ ComputablePred p) (hcompl : REPred fun a => ¬ p a) :
    ¬ REPred p := by
  intro hpRe
  exact hp (ComputablePred.computable_iff_re_compl_re'.2 ⟨hpRe, hcompl⟩)

theorem not_re_of_manyOneReducible
    {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α → Prop} {q : β → Prop}
    (hred : p ≤₀ q) (hp : ¬ REPred p) :
    ¬ REPred q := by
  intro hq
  exact hp (REPred.of_manyOneReducible hred hq)

end InqBQ
end HeytingLean
