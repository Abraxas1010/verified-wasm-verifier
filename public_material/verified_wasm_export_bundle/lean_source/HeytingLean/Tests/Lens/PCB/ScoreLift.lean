import HeytingLean.Lens.PCB.Examples
import HeytingLean.Probability
import HeytingLean.Logic.Booleanization

/-! Compile-only example exercising score-based lifting. -/

namespace HeytingLean
namespace Tests
namespace Lens
namespace PCB

open HeytingLean.Lens.PCB
open HeytingLean.Logic
open HeytingLean.Probability

instance : Inhabited String := ⟨""⟩
instance : DecidableEq String := inferInstance

noncomputable def dLo : Dist (Reg String) :=
  Dist.fromPairs #[("a", 1), ("bbb", 2), ("cccc", 3)]

noncomputable def ms0 : MultiState String :=
  { hiDist := Dist.fromPairs #[("seed", 1)], loDist := dLo }

noncomputable def ms1 : MultiState String :=
  MultiState.update stringScorePolicy ms0 dLo

/-- Updating the multi-state replaces the low-level distribution by `dLo`. -/
example : ms1.loDist = dLo := rfl

-- Tiny argmin demonstration using Distance/Score (compile-only)
open HeytingLean.Lens.PCB in
noncomputable def bestOf (xs : Array String) : Option (Nat × String × Real) :=
  chooseArgmin xs (fun s => (Score.score s) + (Distance.dist s "target"))

end PCB
end Lens
end Tests
end HeytingLean
