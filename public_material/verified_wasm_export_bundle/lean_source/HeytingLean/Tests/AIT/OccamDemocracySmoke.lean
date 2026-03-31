import HeytingLean.Meta.AIT.OccamDemocracy

/-
Compile-time smoke tests for democratic model voting.

These examples instantiate `ModelFamily` on a tiny finite type and
exercise the basic voting and bounded-voting definitions. They are
kept deliberately small and are intended to guard against regressions
in the AIT layer.
-/

namespace HeytingLean.Tests.AIT

open HeytingLean.Meta.AIT

def sampleFamily : ModelFamily Nat Nat Bool :=
  { models     := [0, 1, 2]
    code       := fun n => if n = 0 then [false] else [true]
    predict    := fun n _ => n % 2 = 0
    consistent := fun _ _ => true }

example : sampleFamily.voteCount (past := 0) (out := true) ≥ 0 := by
  have := sampleFamily.voteCount_nonneg (past := 0) (out := true)
  simpa using this

example : sampleFamily.voteCountBounded (past := 0) (out := true) (L := 1) ≥ 0 := by
  have := sampleFamily.voteCountBounded_nonneg (past := 0) (out := true) (L := 1)
  simpa using this

-- Occam preference is a well-typed predicate we can form on scenarios.
example : Prop :=
  sampleFamily.occamPreference (past := 0) (outSimple := true) (outComplex := false) (L := 1)

end HeytingLean.Tests.AIT
