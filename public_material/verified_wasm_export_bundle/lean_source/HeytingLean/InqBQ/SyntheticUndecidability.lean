import HeytingLean.InqBQ.Computability
import HeytingLean.InqBQ.RecEnumBridge

namespace HeytingLean
namespace InqBQ

/-- Coq-style complement on predicates. -/
def CoqComplement {α : Type*} (p : α → Prop) : α → Prop :=
  fun x => ¬ p x

/-- Coq-style enumeration witness. -/
def CoqEnumerator {α : Type*} (f : Nat → Option α) (p : α → Prop) : Prop :=
  ∀ x, p x ↔ ∃ n, f n = some x

/-- Coq-style enumerability. -/
def CoqEnumerable {α : Type*} (p : α → Prop) : Prop :=
  ∃ f : Nat → Option α, CoqEnumerator f p

/-- Coq-style many-one reduction witness. -/
def CoqReduction {α β : Type*} (f : α → β) (p : α → Prop) (q : β → Prop) : Prop :=
  ∀ x, p x ↔ q (f x)

/-- Coq-style many-one reducibility. -/
def CoqReduces {α β : Type*} (p : α → Prop) (q : β → Prop) : Prop :=
  ∃ f : α → β, CoqReduction f p q

/--
Coq synthetic undecidability relative to an explicit base problem.
This packages the shape used in the external library:
decidability of `p` would enumerate the complement of `base`.
-/
def CoqUndecidable {α β : Type*} (base : β → Prop) (p : α → Prop) : Prop :=
  CoqDecidable p → CoqEnumerable (CoqComplement base)

theorem coqReduction_transitive
    {α β γ : Type*} {p : α → Prop} {q : β → Prop} {r : γ → Prop}
    {f : α → β} {g : β → γ}
    (hf : CoqReduction f p q) (hg : CoqReduction g q r) :
    CoqReduction (fun x => g (f x)) p r := by
  intro x
  exact (hf x).trans (hg (f x))

theorem coqReduces_complement
    {α β : Type*} {p : α → Prop} {q : β → Prop}
    (hred : CoqReduces p q) :
    CoqReduces (CoqComplement p) (CoqComplement q) := by
  rcases hred with ⟨f, hf⟩
  refine ⟨f, ?_⟩
  intro x
  simpa [CoqComplement] using not_congr (hf x)

theorem coqUndecidable_of_reduces
    {α β γ : Type*} {base : γ → Prop} {p : α → Prop} {q : β → Prop}
    (hundec : CoqUndecidable base p) (hred : CoqReduces p q) :
    CoqUndecidable base q := by
  intro hq
  rcases hred with ⟨f, hf⟩
  apply hundec
  rcases hq with ⟨d, hd⟩
  refine ⟨fun x => d (f x), ?_⟩
  intro x
  exact (hf x).trans (hd (f x))

theorem coqDecidable_of_computablePred
    {α : Type*} [Primcodable α] {p : α → Prop}
    (hp : ComputablePred p) :
    CoqDecidable p := by
  rcases ComputablePred.computable_iff.1 hp with ⟨b, hb, hpEq⟩
  refine ⟨b, ?_⟩
  intro x
  simpa [CoqReflects, hpEq]

theorem not_computable_of_coqUndecidable
    {α β : Type*} [Primcodable α] {base : β → Prop} {p : α → Prop}
    (hundec : CoqUndecidable base p)
    (hbase : ¬ CoqEnumerable (CoqComplement base)) :
    ¬ ComputablePred p := by
  intro hp
  exact hbase (hundec (coqDecidable_of_computablePred hp))

theorem not_re_of_coqUndecidable_complement
    {α β : Type*} [Primcodable α] {base : β → Prop} {p : α → Prop}
    (hundec : CoqUndecidable base (CoqComplement p))
    (hbase : ¬ CoqEnumerable (CoqComplement base))
    (hpRe : REPred p) :
    ¬ REPred (CoqComplement p) := by
  classical
  refine not_re_of_not_computable_of_re_compl
    (not_computable_of_coqUndecidable hundec hbase) ?_
  exact REPred.of_eq hpRe (fun x => by simp [CoqComplement])

end InqBQ
end HeytingLean
