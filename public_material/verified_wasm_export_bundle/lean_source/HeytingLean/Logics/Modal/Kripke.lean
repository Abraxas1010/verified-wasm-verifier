import Mathlib.Order.Heyting.Basic

namespace HeytingLean.Logics.Modal

/-- A Kripke frame: set of worlds with accessibility relation -/
structure Frame (W : Type*) where
  rel : W → W → Prop

/-- Modal propositional formulas -/
inductive Formula (Var : Type*) where
  | var : Var → Formula Var
  | bot : Formula Var
  | imp : Formula Var → Formula Var → Formula Var
  | conj : Formula Var → Formula Var → Formula Var
  | disj : Formula Var → Formula Var → Formula Var
  | box : Formula Var → Formula Var
  | dia : Formula Var → Formula Var
  deriving Repr

/-- A Kripke model: frame + valuation -/
structure Model (W : Type*) (Var : Type*) extends Frame W where
  val : W → Var → Prop

/-- Satisfaction relation: world w satisfies formula φ in model M -/
def satisfies {W : Type*} {Var : Type*} (M : Model W Var) : W → Formula Var → Prop
  | _, .bot => False
  | w, .var p => M.val w p
  | w, .imp φ ψ => satisfies M w φ → satisfies M w ψ
  | w, .conj φ ψ => satisfies M w φ ∧ satisfies M w ψ
  | w, .disj φ ψ => satisfies M w φ ∨ satisfies M w ψ
  | w, .box φ => ∀ v, M.rel w v → satisfies M v φ
  | w, .dia φ => ∃ v, M.rel w v ∧ satisfies M v φ

end HeytingLean.Logics.Modal
