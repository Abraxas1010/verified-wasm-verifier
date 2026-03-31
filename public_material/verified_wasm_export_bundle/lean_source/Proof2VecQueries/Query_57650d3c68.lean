import Mathlib

-- Intentionally OUTSIDE the HeytingLean.* namespace so it is not ingested by DB_PREFIX=HeytingLean.
namespace Proof2VecQueries

theorem q : Irrational (Real.sqrt 2) := by
  simpa using irrational_sqrt_two

end Proof2VecQueries

