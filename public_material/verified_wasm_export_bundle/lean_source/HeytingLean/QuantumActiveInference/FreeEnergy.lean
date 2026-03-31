import HeytingLean.ActiveInference.FreeEnergy
import HeytingLean.ActiveInference.AdelicFreeEnergy

/-!
# QuantumActiveInference.FreeEnergy

Bridges the repo’s existing (classical) active inference scaffolding into the unified-system
namespace. The “quantum” specialization lives elsewhere (`HeytingLean.Quantum.ActiveInference.*`);
this module provides the glue types used by lane-changing ATP and sheaf gluing.
-/

namespace HeytingLean
namespace QuantumActiveInference

open HeytingLean.Embeddings
open HeytingLean.ActiveInference

/-- Alias: lens-indexed free energy is the repo’s adelic free-energy record. -/
abbrev LensFreeEnergy :=
  ActiveInference.AdelicFreeEnergy

/-- A simple weighted “Platonic consensus” aggregator over per-lens scalar summaries. -/
def platonicConsensus (w x : LensID → ℝ) : ℝ :=
  w LensID.omega * x LensID.omega +
  w LensID.region * x LensID.region +
  w LensID.graph * x LensID.graph +
  w LensID.clifford * x LensID.clifford +
  w LensID.tensor * x LensID.tensor +
  w LensID.topology * x LensID.topology +
  w LensID.matula * x LensID.matula

theorem platonicConsensus_self (w x : LensID → ℝ) :
    platonicConsensus w x = platonicConsensus w x := by
  rfl

end QuantumActiveInference
end HeytingLean
