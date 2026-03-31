import HeytingLean.QuantumActiveInference.MarkovBlanket
import HeytingLean.QuantumActiveInference.FreeEnergy
import HeytingLean.ActiveInference.Agent

/-!
# QuantumActiveInference.LensActiveInference

Lens-indexed active inference wrappers.

This is intentionally “small surface area”: the repo already has rich per-lens machinery
(LoF lenses, certified transport, quantum active inference). This module records the *glue types*
used by the unified-system spec and by lane-changing ATP.
-/

namespace HeytingLean
namespace QuantumActiveInference

open HeytingLean.Embeddings
open HeytingLean.ActiveInference

/-- A lens-indexed family of Markov blankets. -/
abbrev LensBlankets :=
  LensID → HolographicMarkovBlanket

/-- A lens-indexed family of (classical) active inference agents. -/
abbrev LensAgents (O S A : Type*) :=
  LensID → Agent O S A

/-- A unified lens-indexed agent bundle. -/
structure AdelicActiveInference (O S A : Type*) where
  blankets : LensBlankets
  agents : LensAgents O S A
  weights : LensID → ℝ

/-- A simple (executable) total objective: weighted sum of per-lens free energies at a single observation. -/
noncomputable def totalObjective {O S A : Type*} [Fintype S]
    (U : AdelicActiveInference O S A) (obs : LensID → O) : ℝ :=
  let per : LensID → ℝ :=
    fun lens =>
      freeEnergy (U.agents lens).generativeModel (U.agents lens).recognitionModel (obs lens)
  platonicConsensus U.weights per

theorem totalObjective_self {O S A : Type*} [Fintype S]
    (U : AdelicActiveInference O S A) (obs : LensID → O) :
    totalObjective U obs = totalObjective U obs := by
  rfl

end QuantumActiveInference
end HeytingLean

