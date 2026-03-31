import HeytingLean.Logic.PSR

namespace Proof2VecQueries

open HeytingLean
open HeytingLean.LoF
open HeytingLean.Epistemic
open HeytingLean.Logic.PSR

variable {α : Type} [HeytingLean.PrimaryAlgebra α]

-- Query is outside `HeytingLean.*` so it is not ingested into the DB.
-- The statement is in-domain: it exercises the PSR/nucleus breathing invariance lemma.
theorem q (R : HeytingLean.LoF.Reentry α) {a x : α}
    (ha : HeytingLean.Logic.PSR.Sufficient R a) (hx : x ≤ a) :
    ∀ n, HeytingLean.Epistemic.breathe (R := R) n x ≤ a := by
  simpa using HeytingLean.Logic.PSR.breathe_le_of_sufficient (R := R) (a := a) (x := x) ha hx

end Proof2VecQueries

