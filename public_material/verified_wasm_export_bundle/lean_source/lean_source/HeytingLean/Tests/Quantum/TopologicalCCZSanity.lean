import Mathlib.Tactic

import HeytingLean.Quantum.TopologicalCCZ

namespace HeytingLean
namespace Tests
namespace Quantum

open HeytingLean.Quantum.TopologicalCCZ

/-! Compile-time sanity checks for Phase 7 (topological CCZ statement packaging). -/

namespace CCZDemo

private abbrev ψ : Ket Int := fun _ => 1

example : (CCZ (𝕜 := Int) ψ) ket111 = -1 := by
  simp [CCZ, cczLike, ψ, ket111]

example (q : Q3) (hq : q ≠ ket111) : (CCZ (𝕜 := Int) ψ) q = 1 := by
  simp [CCZ, cczLike, ψ, hq]

example : (cczLike (𝕜 := Int) (0 : ZMod 2) ψ) = ψ := by
  simp [cczLikeLemmas.eq_self_of_eq_zero (𝕜 := Int) ψ]

end CCZDemo

namespace StatementDemo

private def topo : TripleIntersectionModel Unit where
  Cycle := Unit
  triple := fun _ _ _ => (1 : ZMod 2)

private def S : CCZFromTripleIntersection (T := Unit) (𝕜 := Int) where
  topo := topo
  membrane := fun _ => ()
  topoGate := CCZ (𝕜 := Int)
  gate_spec := by
    intro ψ q
    -- `parity = 1`, so the specification is exactly CCZ = cczLike 1.
    simp [topo, CCZ, cczLike]

example : S.parity = 1 := by
  rfl

example : S.topoGate = CCZ (𝕜 := Int) := by
  simpa using (S.topoGate_eq_CCZ_of_parity_one (T := Unit) (𝕜 := Int) (h := rfl))

end StatementDemo

end Quantum
end Tests
end HeytingLean
