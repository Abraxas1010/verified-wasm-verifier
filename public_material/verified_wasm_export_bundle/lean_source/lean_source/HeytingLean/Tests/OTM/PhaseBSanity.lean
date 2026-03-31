import HeytingLean.OTM.Invariants

namespace HeytingLean.Tests.OTM

open CategoryTheory
open HeytingLean.OTM

example {ι α : Type} [SemilatticeInf α] [OrderBot α] [DecidableEq ι]
    {N : RNucleus α} (T : Tape ι α N) (i j : ι) (v : α) (hv : N.R v = v) :
    N.R ((Tape.write T i v hv).read j) = (Tape.write T i v hv).read j :=
  otm_tape_write_preserves_fixed T i j v hv

example {ι α : Type} [DecidableEq ι] [LoF.PrimaryAlgebra α]
    (M : Machine ι α) (i : ι) :
    M.nucleus.core.R ((M.step).tape.read i) = (M.step).tape.read i :=
  otm_step_preserves_fixed_cells M i

example {ι α : Type} [DecidableEq ι] [LoF.PrimaryAlgebra α]
    (M : Machine ι α) (fuel : Nat) (i : ι) :
    M.nucleus.core.R ((Machine.run fuel M).tape.read i) =
      (Machine.run fuel M).tape.read i :=
  otm_run_preserves_fixed_cells M fuel i

example {Ωα : Type} [LoF.PrimaryAlgebra Ωα]
    {C : Type} [Category C]
    [CategoryTheory.Limits.HasPullbacks C]
    [CategoryTheory.HasClassifier C]
    (B : PerspectivalPlenum.ReentryLTBridge Ωα C) (p : Ωα) :
    B.R.nucleus p = p ↔
      Topos.LTfromNucleus.reclassify (C := C) B.ltKit.j (B.truthEquiv p) = B.truthEquiv p :=
  otm_reentry_fixed_iff_lt_closed B p

end HeytingLean.Tests.OTM
