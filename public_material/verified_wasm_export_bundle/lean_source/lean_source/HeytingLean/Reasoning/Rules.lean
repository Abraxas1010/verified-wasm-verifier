/-
Reasoning rules: minimal data structures and helpers.
-/

namespace HeytingLean
namespace Reasoning

structure Rule (α : Type u) where
  premises : Array α
  concl    : α
deriving Repr

namespace Rule
variable {α : Type u} [DecidableEq α]

@[simp] def isTriggered (r : Rule α) (facts : Array α) : Bool :=
  r.premises.all (fun p => facts.contains p)

@[simp] def apply (r : Rule α) (facts : Array α) : Option α :=
  if r.isTriggered facts ∧ ¬ facts.contains r.concl then
    some r.concl
  else
    none

end Rule

end Reasoning
end HeytingLean

