import HeytingLean.Bridges.Archetype.MagnitudeEigenformSynthesis

namespace HeytingLean
namespace Bridges
namespace Archetype

/-- Directed paths in the archetype bridge network. -/
inductive BridgePath : ArchetypeNode → ArchetypeNode → Type where
  | nil : (a : ArchetypeNode) → BridgePath a a
  | cons : {a b c : ArchetypeNode} →
      hasDirectedBridge a b → BridgePath b c → BridgePath a c

/-- Path length in number of directed edges. -/
def BridgePath.length : BridgePath a b → Nat
  | .nil _ => 0
  | .cons _ p => 1 + p.length

/-- Concatenate composable directed paths. -/
def BridgePath.append : BridgePath a b → BridgePath b c → BridgePath a c
  | .nil _, q => q
  | .cons h p, q => .cons h (p.append q)

/-- Length is additive under path concatenation. -/
theorem BridgePath.length_append (p : BridgePath a b) (q : BridgePath b c) :
    (p.append q).length = p.length + q.length := by
  induction p with
  | nil _ =>
      simp [BridgePath.append, BridgePath.length]
  | cons h p ih =>
      simp [BridgePath.append, BridgePath.length, ih, Nat.add_assoc]

/-- Non-trivial directed self-reachability. -/
def hasSelfLoop (a : ArchetypeNode) : Prop :=
  ∃ p : BridgePath a a, 0 < p.length

/-- One-step bridge distance model (`none` for missing direct bridge). -/
def bridgeDistance (a b : ArchetypeNode) : Option Nat :=
  if a = b then some 0
  else if _h : hasDirectedBridge a b then some 1
  else none

theorem bridgeDistance_self (a : ArchetypeNode) :
    bridgeDistance a a = some 0 := by
  simp [bridgeDistance]

theorem bridgeDistance_of_directed {a b : ArchetypeNode}
    (hne : a ≠ b) (hdir : hasDirectedBridge a b) :
    bridgeDistance a b = some 1 := by
  simp [bridgeDistance, hne, hdir]

theorem bridgeDistance_none_of_no_direct {a b : ArchetypeNode}
    (hne : a ≠ b) (hndir : ¬ hasDirectedBridge a b) :
    bridgeDistance a b = none := by
  simp [bridgeDistance, hne, hndir]

/-- A height ranking that strictly decreases along every declared directed bridge. -/
def nodeHeight : ArchetypeNode → Nat
  | .rNucleus => 0
  | .jRatchet => 0
  | .oscillatory => 0
  | .lens => 0
  | .adelic => 0
  | .kanExtension => 1
  | .monadKleisli => 1
  | .magnitude => 1
  | .dialectica => 2
  | .condensed => 1
  | .polynomial => 1
  | .spectralSequence => 1
  | .connection => 1
  | .yoneda => 1
  | .measure => 1
  | .opetope => 0
  | .barConstruction => 2

/-- Every declared directed bridge strictly decreases `nodeHeight`. -/
theorem directedBridge_strictly_decreases :
    ∀ a b : ArchetypeNode, hasDirectedBridge a b → nodeHeight b < nodeHeight a := by
  decide

/-- Any positive-length path strictly decreases `nodeHeight` from source to target. -/
theorem path_target_lt_source_of_pos {a b : ArchetypeNode}
    (p : BridgePath a b) (hpos : 0 < p.length) :
    nodeHeight b < nodeHeight a := by
  cases p with
  | nil _ =>
      cases Nat.not_lt_zero _ hpos
  | cons h p =>
      cases p with
      | nil _ =>
          simpa [BridgePath.length] using directedBridge_strictly_decreases _ _ h
      | cons h₂ p₂ =>
          have htailPos : 0 < (BridgePath.cons h₂ p₂).length := by
            simp [BridgePath.length]
          have htail : nodeHeight _ < nodeHeight _ :=
            path_target_lt_source_of_pos (BridgePath.cons h₂ p₂) htailPos
          have hhead : nodeHeight _ < nodeHeight _ := directedBridge_strictly_decreases _ _ h
          exact lt_trans htail hhead

/-- The declared bridge network has no directed self-loops. -/
theorem no_self_loops_in_bridge_network :
    ∀ a : ArchetypeNode, ¬ hasSelfLoop a := by
  intro a hloop
  rcases hloop with ⟨p, hpos⟩
  have hlt : nodeHeight a < nodeHeight a := path_target_lt_source_of_pos p hpos
  exact Nat.lt_irrefl _ hlt

end Archetype
end Bridges
end HeytingLean
