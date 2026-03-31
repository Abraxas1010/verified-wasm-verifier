import HeytingLean.LeanClef.Inet.Combinators
import HeytingLean.LeanClef.PHG.CliffordGrade

/-!
# LeanClef.Inet.GradedInet

Extend the Inet formalization with Clifford grade annotations.

Reference: Haynes arXiv:2603.17627, Section 7.3
-/

namespace LeanClef.Inet

open LeanClef.PHG

/-- A graded agent carries grade annotations on its ports. -/
structure GradedAgent (cl : CliffordAlgebra) where
  kind : CombinatorKind
  id : Nat
  principalGrade : Grade cl
  auxGrades : List (Grade cl)
  arity_match : auxGrades.length = kind.arity

/-- A graded net state. -/
structure GradedInetState (cl : CliffordAlgebra) where
  agents : Array (Option (GradedAgent cl))
  wires : List Wire

/-- Erase grade annotations, yielding an ungraded InetState. -/
def GradedInetState.toUngraded (s : GradedInetState cl) : InetState :=
  { agents := s.agents.map (Option.map fun a => { kind := a.kind, id := a.id })
    wires := s.wires }

/-- Look up the grade at a given port of a graded agent. -/
def GradedAgent.gradeAtPort (a : GradedAgent cl) (portIdx : Nat) : Option (Grade cl) :=
  if portIdx = 0 then some a.principalGrade
  else a.auxGrades[portIdx - 1]?

/-- Look up the grade at a port in the net. -/
def GradedInetState.gradeAt (s : GradedInetState cl) (agentId portIdx : Nat) :
    Option (Grade cl) := do
  let agentOpt ← s.agents[agentId]?
  let agent ← agentOpt
  agent.gradeAtPort portIdx

/-- Grade consistency: for every wire, connected ports carry the same grade. -/
def GradedInetState.gradeConsistent (s : GradedInetState cl) : Prop :=
  ∀ w ∈ s.wires,
    ∀ g1 g2 : Grade cl,
      s.gradeAt w.agent1 w.port1 = some g1 →
      s.gradeAt w.agent2 w.port2 = some g2 →
      g1 = g2

/-- Annihilation grade safety: if two agents in a grade-consistent net
    are connected at their principal ports AND have matching auxiliary
    grades at each index, then reconnecting aux[i] of one to aux[i]
    of the other preserves grade consistency at each reconnected wire.

    The key content: the aux-grade-matching hypothesis
    (h_aux_eq) is the structural invariant that graded typing must
    maintain. Grade consistency of the NET (matching endpoints on
    existing wires) does NOT alone imply matching aux grades between
    interacting agents — that requires the graded typing discipline.

    We prove: given matching aux grades, the reconnection is safe
    (any grade extracted from either side agrees). -/
theorem annihilation_preserves_grades (cl : CliffordAlgebra)
    (s : GradedInetState cl)
    (h_gc : s.gradeConsistent)
    (a1_id a2_id : Nat)
    (w : Wire) (h_w : w ∈ s.wires)
    (h_pp : w.port1 = 0 ∧ w.port2 = 0)
    (h_agents : w.agent1 = a1_id ∧ w.agent2 = a2_id)
    (a1 a2 : GradedAgent cl)
    (h_a1 : s.agents[a1_id]? = some (some a1))
    (h_a2 : s.agents[a2_id]? = some (some a2))
    (h_same : a1.kind = a2.kind)
    (h_aux_eq : ∀ i : Nat, i < a1.auxGrades.length →
      a1.auxGrades[i]? = a2.auxGrades[i]?) :
    -- Principal grades match (from grade consistency)
    a1.principalGrade = a2.principalGrade ∧
    -- Arity match (from kind equality + arity_match fields)
    a1.auxGrades.length = a2.auxGrades.length ∧
    -- Aux grades match pairwise (from h_aux_eq)
    (∀ i : Nat, i < a1.auxGrades.length →
      ∀ g1 g2 : Grade cl,
        a1.auxGrades[i]? = some g1 →
        a2.auxGrades[i]? = some g2 →
        g1 = g2) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Principal grades match via grade consistency on the principal wire
    have hg := h_gc w h_w
    have h_g1 : s.gradeAt w.agent1 w.port1 = some a1.principalGrade := by
      simp [GradedInetState.gradeAt, h_agents.1, h_a1,
            GradedAgent.gradeAtPort, h_pp.1]
    have h_g2 : s.gradeAt w.agent2 w.port2 = some a2.principalGrade := by
      simp [GradedInetState.gradeAt, h_agents.2, h_a2,
            GradedAgent.gradeAtPort, h_pp.2]
    exact hg a1.principalGrade a2.principalGrade h_g1 h_g2
  · -- Arity match: same kind → same arity → same aux length
    rw [a1.arity_match, h_same, ← a2.arity_match]
  · -- Aux grades match from the hypothesis
    intro i hi g1 g2 hg1 hg2
    have := h_aux_eq i hi
    rw [hg1, hg2] at this
    exact Option.some.inj this

/-- Grade consistency applies to all wires: connected ports carry
    the same grade. This is a direct application of gradeConsistent. -/
theorem wire_grades_match (cl : CliffordAlgebra)
    (s : GradedInetState cl)
    (h_gc : s.gradeConsistent)
    (w : Wire) (h_w : w ∈ s.wires)
    (g1 g2 : Grade cl)
    (h_g1 : s.gradeAt w.agent1 w.port1 = some g1)
    (h_g2 : s.gradeAt w.agent2 w.port2 = some g2) :
    g1 = g2 :=
  h_gc w h_w g1 g2 h_g1 h_g2

end LeanClef.Inet
