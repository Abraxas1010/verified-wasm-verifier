import HeytingLean.MirandaDynamics.Billiards.CantorEncoding
import HeytingLean.MirandaDynamics.Billiards.CantorNucleus
import HeytingLean.MirandaDynamics.Topology.BettiComplexity

namespace HeytingLean
namespace Tests
namespace MirandaDynamics

open HeytingLean.MirandaDynamics

namespace Billiards

open HeytingLean.MirandaDynamics.Billiards

example (z : ℤ) : tapeIndex (indexNat z) = z :=
  tapeIndex_indexNat z

example : headInterval_reflect (-1 : ℤ) (x := (1 / 9 : ℝ)) := by
  simpa using (headInterval_reflect (-1 : ℤ) (x := (1 / 9 : ℝ)))

example : Disjoint (headInterval (-1 : ℤ)) (headInterval (0 : ℤ)) := by
  have h : (-1 : ℤ) ≠ 0 := by norm_num
  exact headInterval_disjoint (-1 : ℤ) 0 h

example (t : Tape) (k : ℤ) :
    encodeWithHead t (k + 1) =
      (if k < 0 then 3 * encodeWithHead t k else encodeWithHead t k / 3 + 2 / 3) := by
  simpa using encodeWithHead_shift t k

example (S : Set ℝ) : cantorNucleus S = S ↔ cantorCompl ⊆ S :=
  cantorNucleus_fixed_iff (S := S)

end Billiards

namespace Topology

open HeytingLean.MirandaDynamics.Topology

variable {V : Type} (G : SimpleGraph V)

example [Finite V] (h : G.IsTree) : cycleRank G = 0 :=
  cycleRank_eq_zero_of_isTree (G := G) h

end Topology

end MirandaDynamics
end Tests
end HeytingLean

