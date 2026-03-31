import HeytingLean.ModalCategorySets.Propositional.Core

namespace HeytingLean.ModalCategorySets.Propositional

universe u

variable {α : Type u}

/-- K: `□(p → q) → (□p → □q)`. -/
def axiomK (p q : α) : Formula α :=
  .imp (.box (.imp (.var p) (.var q)))
    (.imp (.box (.var p)) (.box (.var q)))

/-- T: `□p → p`. -/
def axiomT (p : α) : Formula α :=
  .imp (.box (.var p)) (.var p)

/-- 4: `□p → □□p`. -/
def axiom4 (p : α) : Formula α :=
  .imp (.box (.var p)) (.box (.box (.var p)))

/-- 5: `◇p → □◇p`. -/
def axiom5 (p : α) : Formula α :=
  .imp (.dia (.var p)) (.box (.dia (.var p)))

/-- `.2`: `◇□p → □◇p`. -/
def axiomDot2 (p : α) : Formula α :=
  .imp (.dia (.box (.var p))) (.box (.dia (.var p)))

/-- `.3`: `□(□p → q) ∨ □(□q → p)`. -/
def axiomDot3 (p q : α) : Formula α :=
  .disj (.box (.imp (.box (.var p)) (.var q)))
    (.box (.imp (.box (.var q)) (.var p)))

/-- Triviality: `p ↔ □p`. -/
def axiomTriv (p : α) : Formula α :=
  Formula.iff (.var p) (.box (.var p))

/-- Grzegorczyk's axiom in the paper's propositional syntax. -/
def axiomGrz (p : α) : Formula α :=
  .imp (.box (.imp (.box (.imp (.var p) (.box (.var p)))) (.var p))) (.var p)

end HeytingLean.ModalCategorySets.Propositional
