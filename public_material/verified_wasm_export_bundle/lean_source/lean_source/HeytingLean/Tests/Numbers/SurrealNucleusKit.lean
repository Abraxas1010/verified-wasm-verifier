import HeytingLean.Generative.SurrealNucleusKit

open HeytingLean
open HeytingLean.Numbers
open HeytingLean.Numbers.Surreal
open HeytingLean.Generative

/-! Smoke tests for the Surreal-specific interior nucleus kit. -/

#check Generative.SurrealNucleusKit.Carrier
#check Generative.SurrealNucleusKit.breathe
#check Generative.SurrealNucleusKit.birth
#check Generative.SurrealNucleusKit.occam

noncomputable section
  open SurrealNucleusKit

  variable (S : Carrier)

  example : breathe 0 S = S := by
    simpa using breathe_zero (S := S)

  example : surrealIntReentry (occam S) = occam S := by
    simpa using occam_idem (S := S)

  example : birth S = 0 ↔ surrealIntReentry S = S := by
    simpa using birth_eq_zero_iff (S := S)
end
