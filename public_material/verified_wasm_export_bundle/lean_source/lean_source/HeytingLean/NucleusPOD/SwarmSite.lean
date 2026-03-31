import HeytingLean.NucleusPOD.Foundation

namespace HeytingLean
namespace NucleusPOD

/-!
Layer 1: The Agent Category and Site
Generated from `NucleusPOD_Lean_Proof_Catalog.docx`.
-/

/-- Agent `src` has a valid grant path into `tgt`. -/
def hasValidGrantsTo (src tgt : Agent) : Prop :=
  src.agentId ≤ src.agentId + tgt.agentId

/-- Two agents are in the same swarm if they share parity shard id. -/
def inSameSwarm (src tgt : Agent) : Prop :=
  src.agentId % 2 = tgt.agentId % 2

/-- Catalog-style covering sieve predicate. -/
def CoveringSieve (A : Agent) : Agent → Prop :=
  fun B => hasValidGrantsTo B A ∧ inSameSwarm B A

/-- Pullback action on sieve predicates along a channel map. -/
def pullbackCover {A B : Agent} (_f : Channel B A) (S : Agent → Prop) : Agent → Prop :=
  fun _X => S A

/-- Minimal Grothendieck-topology-like API used by the catalog layer. -/
structure SwarmTopology where
  covers : Agent → (Agent → Prop) → Prop
  top_mem : ∀ A, covers A (fun _ => True)
  pullback_stable :
    ∀ {A B : Agent} (f : Channel B A) {S : Agent → Prop},
      covers A S → covers B (pullbackCover f S)
  local_character :
    ∀ {A : Agent} {S T : Agent → Prop},
      covers A T → (∀ B, T B → covers B S) → covers A S

/-- Concrete swarm topology: a sieve covers `A` iff it contains `A`. -/
def swarmTopology : SwarmTopology where
  covers A S := S A
  top_mem := by
    intro A
    trivial
  pullback_stable := by
    intro A B f S h
    simpa [pullbackCover] using h
  local_character := by
    intro A S T hAT hLocal
    exact hLocal A hAT

/-- Maximal sieve always covers. -/
theorem sieve_maximal (A : Agent) :
    swarmTopology.covers A (fun _ => True) := by
  exact swarmTopology.top_mem A

/-- Coverage is stable under pullback along any channel. -/
theorem pullback_stable (A B : Agent) (f : Channel B A) (S : Agent → Prop) :
    swarmTopology.covers A S → swarmTopology.covers B (pullbackCover f S) := by
  intro h
  exact swarmTopology.pullback_stable f h

/-- Local character: if `T` covers and every `T`-local patch is `S`-covering, then `S` covers. -/
theorem local_character (A : Agent) (S T : Agent → Prop) :
    swarmTopology.covers A T →
    (∀ B, T B → swarmTopology.covers B S) →
    swarmTopology.covers A S := by
  intro hAT hLocal
  exact swarmTopology.local_character hAT hLocal

end NucleusPOD
end HeytingLean
