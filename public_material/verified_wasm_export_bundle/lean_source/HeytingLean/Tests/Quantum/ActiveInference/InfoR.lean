import HeytingLean.Quantum.ActiveInference.InfoR

/-! Compile-only sanity for InfoR (KL, EFE, argmin). -/

namespace HeytingLean.Quantum.ActiveInference

open ActiveInference

def p : Array ℝ := #[0.5, 0.5]
def q : Array ℝ := #[0.5, 0.5]

def einputs : EFEInputs := { costs := #[1.0, 2.0], post := p, prior := q }

-- compile-only: avoid runtime eval to keep test pure
noncomputable def _sanity1 : ℝ := klDivR p q
noncomputable def _sanity2 : ℝ := efeR einputs
noncomputable def _sanity3 : Nat × ℝ := argminIdx [3.0, -2.0, 1.5]

end HeytingLean.Quantum.ActiveInference
