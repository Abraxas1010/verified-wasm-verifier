import HeytingLean.Reasoning.Rules

/-
Forward-chaining engine over arrays of facts and rules.
Purely functional and compile-friendly; bounded by `maxSteps`.
-/

namespace HeytingLean
namespace Reasoning

open Rule

variable {α : Type u} [DecidableEq α]

@[simp] def addIfNew (facts : Array α) (a : α) : Array α :=
  if facts.contains a then facts else facts.push a

@[simp] def step (rules : Array (Rule α)) (facts : Array α) : Array α :=
  rules.foldl (init := facts) (fun acc r =>
    match r.apply acc with
    | some c => addIfNew acc c
    | none   => acc)

@[simp] def saturate (rules : Array (Rule α))
    (facts : Array α) (maxSteps : Nat := 64) : Array α :=
  let rec go (k : Nat) (f : Array α) : Array α :=
    if k = 0 then f
    else
      let f' := step rules f
      if f'.size = f.size then f else go (k - 1) f'
  go maxSteps facts

end Reasoning
end HeytingLean

