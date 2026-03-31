import HeytingLean.Logics.Modal.Kripke

namespace HeytingLean.Logics.Modal.S4

open HeytingLean.Logics.Modal

/-- S4 frame: reflexive and transitive -/
structure S4Frame (W : Type*) extends Frame W where
  refl : ∀ w, rel w w
  trans : ∀ u v w, rel u v → rel v w → rel u w

/-- The Gödel translation: intuitionistic → S4 modal -/
def goedelTranslation {Var : Type*} : Formula Var → Formula Var
  | .var p => .box (.var p)
  | .bot => .bot
  | .conj φ ψ => .conj (goedelTranslation φ) (goedelTranslation ψ)
  | .disj φ ψ => .disj (goedelTranslation φ) (goedelTranslation ψ)
  | .imp φ ψ => .box (.imp (goedelTranslation φ) (goedelTranslation ψ))
  | .box φ => .box (goedelTranslation φ)
  | .dia φ => .dia (goedelTranslation φ)

end HeytingLean.Logics.Modal.S4
