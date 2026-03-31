import HeytingLean.OTM.Assembly
import HeytingLean.OTM.ReentryBridge

namespace HeytingLean
namespace OTM

universe u v

/-- Writing a nucleus-fixed value preserves fixedness of all tape reads. -/
theorem otm_tape_write_preserves_fixed
    {ι : Type u} {α : Type v}
    [SemilatticeInf α] [OrderBot α] [DecidableEq ι]
    {N : RNucleus α}
    (T : Tape ι α N) (i j : ι) (v : α) (hv : N.R v = v) :
    N.R ((Tape.write T i v hv).read j) = (Tape.write T i v hv).read j := by
  exact (Tape.read_fixed (T := Tape.write T i v hv) (i := j))

/-- One machine step preserves fixedness of every tape cell. -/
theorem otm_step_preserves_fixed_cells
    {ι : Type u} {α : Type v}
    [DecidableEq ι] [LoF.PrimaryAlgebra α]
    (M : Machine ι α) (i : ι) :
    M.nucleus.core.R ((M.step).tape.read i) = (M.step).tape.read i := by
  exact (Machine.step_tape_fixed (M := M) i)

/-- Fuel-bounded runs preserve fixedness of every tape cell. -/
theorem otm_run_preserves_fixed_cells
    {ι : Type u} {α : Type v}
    [DecidableEq ι] [LoF.PrimaryAlgebra α]
    (M : Machine ι α) :
    ∀ fuel i, M.nucleus.core.R ((Machine.run fuel M).tape.read i) = (Machine.run fuel M).tape.read i := by
  intro fuel
  induction fuel generalizing M with
  | zero =>
      intro i
      exact M.tape.fixed i
  | succ fuel ih =>
      intro i
      simpa [Machine.run] using ih (M := M.step) i

end OTM
end HeytingLean
