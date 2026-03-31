import HeytingLean.Probability

/-! Compile-only sanity for decision helper. -/

namespace HeytingLean
namespace Tests
namespace Probability

open HeytingLean.Probability

noncomputable def smallModel (a : Nat) : Dist Int :=
  if a = 0 then Dist.fromPairs #[(0,1), (10,1)] else Dist.fromPairs #[(5,1), (6,1)]

noncomputable def u (x : Int) : ℝ := (Int.toNat (Int.natAbs x))

/-- Instantiate `expectedUtilityChooser` on a tiny model to ensure the helper
is available and well-typed. -/
noncomputable def _chooserDemo : Option Nat := by
  let _ : Inhabited Int := ⟨0⟩
  let _ : Inhabited Nat := ⟨0⟩
  exact expectedUtilityChooser (#[(0:Nat),(1:Nat)]) smallModel
    (fun x => (Int.toNat (Int.natAbs x)))

end Probability
end Tests
end HeytingLean
