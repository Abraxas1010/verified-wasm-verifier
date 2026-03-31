import HeytingLean.Generative.PrimeStability
import HeytingLean.Bridge.AlMayahi.UDTRecovery.StandardRecoveries

namespace HeytingLean.Tests.Generative.PrimeStability

open HeytingLean.Generative
open HeytingLean.Generative.PrimeStability
open HeytingLean.Bridge.AlMayahi.UDTRecovery

example : Nat.Prime 2 := by decide

example : ¬ Nat.Prime 6 := by decide

example : 2 ∣ 6 ∧ 1 < 2 ∧ 2 < 6 := by decide

example : 3 ∣ 6 ∧ 1 < 3 ∧ 3 < 6 := by decide

example : ∀ p : ℕ, Nat.Prime p → 2 ≤ p := two_is_terminal_prime

example : projectionClassification photonClosure = .boolean := by
  exact identity_projects_boolean photonClosure photon_closure_period_one

example : projectionClassification noneistClosure = .heyting := by
  exact massive_projects_heyting noneistClosure
    (by simpa [noneistClosure, RotationalClosure.period] using electron_massive canonicalElectron)

example : Function.minimalPeriod noneistAxis.step noneistAxis.state₁ = 2 :=
  noneist_axis_period_two

example : standardRecoveries.primeStability = .derived := rfl

example : standardRecoveries.bornHeytingGap = .structuralProxy := rfl

example : standardRecoveries.koideFormula = .parameterizedRecovery := rfl

example :
    signedKoideQ (brannenRoot 1 (2 / 9) 0) (brannenRoot 1 (2 / 9) 1) (brannenRoot 1 (2 / 9) 2) = 2 / 3 := by
  simpa using brannen_gives_signed_koide_exact 1 (2 / 9) (by norm_num)

end HeytingLean.Tests.Generative.PrimeStability
