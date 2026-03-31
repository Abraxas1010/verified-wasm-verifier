import HeytingLean.LoF.HeytingCore
import HeytingLean.Logic.BooleanizationDN

/-! Compile-only sanity for double-negation Booleanization on a concrete
Heyting carrier: Ω = R.Omega for a re-entry nucleus. -/

namespace HeytingLean
namespace Tests
namespace Logic

open HeytingLean.LoF
open HeytingLean.Logic

universe u

variable {α : Type u} [PrimaryAlgebra α]
variable (R : Reentry α)

-- Any element coerces to RegDN via `toBoolDN`.
def xDN : RegDN (R.Omega) := RegDN.toBoolDN (Ω := R.Omega) (R.process)
def yDN : RegDN (R.Omega) := RegDN.toBoolDN (Ω := R.Omega) (R.counterProcess)

-- Commutativity of lifted meet/join holds definitionally under closure.
example : RegDN.inf (xDN (R := R)) (yDN (R := R)) =
          RegDN.inf (yDN (R := R)) (xDN (R := R)) := by
  simpa using (RegDN.inf_commDN (x := xDN (R := R)) (y := yDN (R := R)))

example : RegDN.sup (xDN (R := R)) (yDN (R := R)) =
          RegDN.sup (yDN (R := R)) (xDN (R := R)) := by
  simpa using (RegDN.sup_commDN (x := xDN (R := R)) (y := yDN (R := R)))

-- Top/bottom values reduce as expected.
example : (RegDN.top (Ω := R.Omega)).1 = (⊤ : R.Omega) := by simp
example : (RegDN.bot (Ω := R.Omega)).1 = (⊥ : R.Omega) := by simp

/-! Additional Boolean sanity on a genuinely Boolean carrier. -/

section BooleanCarrier

-- Use `Prop` which has a canonical BooleanAlgebra instance.
example (x : RegDN Prop) : x ⊔ xᶜ = ⊤ := by
  simpa using (sup_compl_eq_top (x := x))

example (x : RegDN Prop) : x ⊓ xᶜ = ⊥ := by
  simpa using (inf_compl_eq_bot' (x := x))

-- Also works for `Bool`.
example (x : RegDN Bool) : x ⊔ xᶜ = ⊤ := by
  simpa using (sup_compl_eq_top (x := x))

example (x : RegDN Bool) : x ⊓ xᶜ = ⊥ := by
  simpa using (inf_compl_eq_bot' (x := x))

end BooleanCarrier

end Logic
end Tests
end HeytingLean
