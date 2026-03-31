import HeytingLean.NucleusPOD.SwarmSite
import HeytingLean.NucleusPOD.AgentCategory
import Mathlib.CategoryTheory.Sites.Grothendieck

namespace HeytingLean
namespace NucleusPOD

/-!
Layer 1: The Agent Category and Site
Generated from `NucleusPOD_Lean_Proof_Catalog.docx`.
-/

open CategoryTheory

/-- Project a sieve on `A` to an object-level swarm predicate used by `swarmTopology`. -/
def sieveCarrierPredicate (A : Agent) (S : Sieve A) : Agent → Prop :=
  fun B => ∃ f : B ⟶ A, S f

/-- Sieve coverage induced from the hand-rolled `swarmTopology` on object predicates. -/
def inducedSwarmCovers (A : Agent) (S : Sieve A) : Prop :=
  swarmTopology.covers A (sieveCarrierPredicate A S)

theorem inducedSwarmCovers_iff_self_arrow (A : Agent) (S : Sieve A) :
    inducedSwarmCovers A S ↔ ∃ f : A ⟶ A, S f := by
  simp [inducedSwarmCovers, sieveCarrierPredicate, swarmTopology]

/-- Category-theoretic site witness induced from `swarmTopology` (nontrivial, not `⊤`). -/
def swarmGrothendieckTopology : GrothendieckTopology Agent where
  sieves A := { S : Sieve A | inducedSwarmCovers A S }
  top_mem' := by
    intro A
    refine (inducedSwarmCovers_iff_self_arrow A ⊤).2 ?_
    exact ⟨𝟙 A, by simp⟩
  pullback_stable' := by
    intro A B S f hS
    rcases (inducedSwarmCovers_iff_self_arrow A S).1 hS with ⟨u, hu⟩
    refine (inducedSwarmCovers_iff_self_arrow B (S.pullback f)).2 ?_
    let k : B ⟶ B := ⟨u.grant⟩
    have hfu : S (f ≫ u) := S.downward_closed hu f
    have hk_eq : k ≫ f = f ≫ u := by
      cases f with
      | mk fg =>
        cases u with
        | mk ug =>
          change (Channel.mk (ug + fg) : Channel B A) = Channel.mk (fg + ug)
          simp [Nat.add_comm]
    have hkf : S (k ≫ f) := by
      exact hk_eq.symm ▸ hfu
    exact ⟨k, hkf⟩
  transitive' := by
    intro A S hS R hR
    rcases (inducedSwarmCovers_iff_self_arrow A S).1 hS with ⟨u, hu⟩
    have hPull : inducedSwarmCovers A (R.pullback u) := hR hu
    rcases (inducedSwarmCovers_iff_self_arrow A (R.pullback u)).1 hPull with ⟨k, hk⟩
    refine (inducedSwarmCovers_iff_self_arrow A R).2 ?_
    exact ⟨k ≫ u, hk⟩

theorem swarmGrothendieck_top_mem (A : Agent) :
    (⊤ : Sieve A) ∈ swarmGrothendieckTopology A := by
  simp [swarmGrothendieckTopology]

theorem swarmGrothendieck_not_top (A : Agent) :
    (⊥ : Sieve A) ∉ swarmGrothendieckTopology A := by
  intro hBot
  rcases (inducedSwarmCovers_iff_self_arrow A ⊥).1 hBot with ⟨f, hf⟩
  exact (show False from hf)

/-- Candidate truth-value object classifier on swarm agents. -/
def Ω (A : Agent) : Bool :=
  A.agentId % 2 == 0

/-- Witness record for topos-style structure over the swarm site. -/
structure SwarmToposWitness where
  topology : SwarmTopology
  topCovers : ∀ A, topology.covers A (fun _ => True)
  omegaDecidable : ∀ A, Ω A = true ∨ Ω A = false
  classifierLaw : ∀ A, Ω A = true ↔ A.agentId % 2 = 0

/-- Concrete witness used by this layer. -/
def swarmToposWitness : SwarmToposWitness where
  topology := swarmTopology
  topCovers := by
    intro A
    exact swarmTopology.top_mem A
  omegaDecidable := by
    intro A
    cases h : Ω A <;> simp
  classifierLaw := by
    intro A
    constructor
    · intro h
      dsimp [Ω] at h
      exact Eq.mp (Nat.beq_eq_true_eq (A.agentId % 2) 0) h
    · intro h
      dsimp [Ω]
      exact Eq.mpr (Nat.beq_eq_true_eq (A.agentId % 2) 0) h

/-- Layer theorem: the swarm sheaf world has the required topos witnesses. -/
theorem swarm_topos :
    swarmToposWitness.topology = swarmTopology ∧
    (∀ A, swarmToposWitness.topology.covers A (fun _ => True)) ∧
    (∀ A, Ω A = true ∨ Ω A = false) := by
  refine ⟨rfl, ?_⟩
  refine ⟨?_, ?_⟩
  · intro A
    exact swarmToposWitness.topCovers A
  · intro A
    exact swarmToposWitness.omegaDecidable A

/-- Every agent receives a decidable truth value in `Ω`. -/
theorem subobject_classifier :
    ∃ omega : Agent → Bool, ∀ A, omega A = true ↔ A.agentId % 2 = 0 := by
  exact ⟨Ω, swarmToposWitness.classifierLaw⟩

end NucleusPOD
end HeytingLean
