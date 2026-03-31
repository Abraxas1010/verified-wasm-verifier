import HeytingLean.Topology.Knot.Burau

/-!
# Sanity checks: Burau braid relations (small)

These are computational proofs that the reduced Burau generator matrices satisfy the Artin braid
relation on 3 strands. This is a minimal correctness guard for the representation itself.
-/

namespace HeytingLean.Tests.Topology.BurauBraidRelations

open HeytingLean.Topology.Knot
open HeytingLean.Topology.Knot.Braid
open HeytingLean.Topology.Knot.Burau

private def σ1 : Braid.Gen := { i := 0, sign := .pos }
private def σ2 : Braid.Gen := { i := 1, sign := .pos }

example :
    Burau.wordReduced 3 [σ1, σ2, σ1] = Burau.wordReduced 3 [σ2, σ1, σ2] := by
  native_decide

example :
    Burau.wordReduced 3 [σ1, σ1.inv] = Except.ok (Burau.matId 2) := by
  native_decide

example :
    Burau.alexanderOfClosedBraid 3 [σ1, σ2, σ1] =
      Burau.alexanderOfClosedBraid 3 [σ2, σ1, σ2] := by
  native_decide

example :
    Burau.alexanderOfClosedBraid 3 [σ1, σ1.inv] =
      Burau.alexanderOfClosedBraid 3 [] := by
  native_decide

end HeytingLean.Tests.Topology.BurauBraidRelations
