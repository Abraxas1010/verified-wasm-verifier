import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace HeytingLean
namespace Probability
namespace InfoTheory

noncomputable section

/-!
Core “information integrand” helpers for finite/discrete information theory.

We use explicit guards so that definitions remain total and proof-friendly:
- `safeLog x = log x` for `x > 0`, and `0` otherwise.
- `klTerm p q` uses a `p ≤ 0` guard to avoid negative-mass artefacts.
- `entropyTerm p` uses the same guard.
-/

def safeLog (x : ℝ) : ℝ := if 0 < x then Real.log x else 0

@[simp] lemma safeLog_of_pos {x : ℝ} (hx : 0 < x) : safeLog x = Real.log x := by
  simp [safeLog, hx]

@[simp] lemma safeLog_of_nonpos {x : ℝ} (hx : x ≤ 0) : safeLog x = 0 := by
  have : ¬ (0 < x) := by exact not_lt_of_ge hx
  simp [safeLog, this]

def klTerm (p q : ℝ) : ℝ :=
  if p ≤ 0 then 0 else p * (safeLog p - safeLog q)

@[simp] lemma klTerm_of_nonpos {p q : ℝ} (hp : p ≤ 0) : klTerm p q = 0 := by
  simp [klTerm, hp]

def entropyTerm (p : ℝ) : ℝ :=
  if p ≤ 0 then 0 else (-p) * safeLog p

@[simp] lemma entropyTerm_of_nonpos {p : ℝ} (hp : p ≤ 0) : entropyTerm p = 0 := by
  simp [entropyTerm, hp]

end

end InfoTheory
end Probability
end HeytingLean

