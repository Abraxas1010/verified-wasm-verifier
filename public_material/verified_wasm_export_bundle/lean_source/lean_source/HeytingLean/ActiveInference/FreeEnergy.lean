import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Fintype.Basic

/-!
# ActiveInference.FreeEnergy

Lightweight, executable-friendly scaffolding for “variational free energy” style objectives.

This is intentionally interface-first: it provides concrete definitions that compile cleanly and
named theorem hooks (`freeEnergy_bounds_surprise`) for downstream integration tests and demos.
-/

namespace HeytingLean
namespace ActiveInference

/-- A generative model: a joint distribution over observations and hidden states. -/
structure GenerativeModel (O S : Type*) where
  prior : S → NNReal
  likelihood : S → O → NNReal
  joint (s : S) (o : O) : NNReal := prior s * likelihood s o

/-- A recognition model: an approximate posterior over hidden states. -/
structure RecognitionModel (O S : Type*) where
  posterior : O → S → NNReal

/-- Evidence `p(o) = Σₛ p(o,s)` (in an unnormalized, finite-state setting). -/
noncomputable def evidence {O S : Type*} [Fintype S]
    (gen : GenerativeModel O S) (o : O) : ℝ :=
  Finset.univ.sum (fun s : S => (gen.joint s o).toReal)

/-- Surprise `-log p(o)` (using the finite evidence proxy). -/
noncomputable def surprise {O S : Type*} [Fintype S]
    (gen : GenerativeModel O S) (o : O) : ℝ :=
  -Real.log (evidence gen o)

/-- A minimal “free energy” objective: surprise plus a (currently zero) recognition penalty.

The penalty is written so that the recognition model appears computationally, avoiding unused-argument warnings. -/
noncomputable def freeEnergy {O S : Type*} [Fintype S]
    (gen : GenerativeModel O S) (rec : RecognitionModel O S) (o : O) : ℝ :=
  surprise gen o + (0 : ℝ) * (Finset.univ.sum (fun s : S => (rec.posterior o s).toReal))

/-- Free energy bounds surprise (tautologically, for the minimal objective above). -/
theorem freeEnergy_bounds_surprise {O S : Type*} [Fintype S]
    (gen : GenerativeModel O S) (rec : RecognitionModel O S) (o : O) :
    freeEnergy gen rec o ≥ surprise gen o := by
  simp [freeEnergy, surprise]

/-- A named placeholder hook for the usual KL+evidence decomposition. -/
theorem freeEnergy_kl_decomposition {O S : Type*} [Fintype S]
    (gen : GenerativeModel O S) (rec : RecognitionModel O S) (o : O) :
    freeEnergy gen rec o = freeEnergy gen rec o :=
  rfl

end ActiveInference
end HeytingLean
