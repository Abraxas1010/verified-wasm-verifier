import HeytingLean.Bridges.ArchetypeRegistry
import HeytingLean.Metrics.Magnitude.Homology
import HeytingLean.Metrics.Magnitude.Weighting
import HeytingLean.Algebra.SpectralSequence.RatchetConvergence

namespace HeytingLean
namespace Bridges
namespace Archetype

/-- Finite object universe for the archetype network. -/
abbrev ArchetypeNode := Bridges.ArchetypeTag

instance : Fintype ArchetypeNode where
  elems := {
    .rNucleus, .jRatchet, .oscillatory, .lens, .adelic,
    .kanExtension, .monadKleisli, .magnitude, .dialectica,
    .condensed, .polynomial, .spectralSequence,
    .connection, .yoneda, .measure, .opetope, .barConstruction
  }
  complete := by
    intro x
    cases x <;> simp

/-- Directed bridge declaration list (the 12 archetype-bridge modules). -/
def declaredDirectedBridges : List (ArchetypeNode × ArchetypeNode) :=
  [ (.kanExtension, .rNucleus)
  , (.monadKleisli, .rNucleus)
  , (.yoneda, .oscillatory)
  , (.dialectica, .oscillatory)
  , (.dialectica, .polynomial)
  , (.polynomial, .lens)
  , (.condensed, .adelic)
  , (.magnitude, .adelic)
  , (.measure, .adelic)
  , (.connection, .lens)
  , (.barConstruction, .spectralSequence)
  , (.spectralSequence, .jRatchet)
  ]

theorem declaredDirectedBridges_count : declaredDirectedBridges.length = 12 := by
  decide

/-- Directed edge predicate induced by the declared bridge list. -/
def hasDirectedBridge (a b : ArchetypeNode) : Prop :=
  (a, b) ∈ declaredDirectedBridges

instance : DecidableRel hasDirectedBridge := by
  intro a b
  unfold hasDirectedBridge
  infer_instance

/-- Undirected adjacency used for chain construction on the bridge network. -/
def bridgeAdjacent (a b : ArchetypeNode) : Prop :=
  hasDirectedBridge a b ∨ hasDirectedBridge b a

instance : DecidableRel bridgeAdjacent := by
  intro a b
  unfold bridgeAdjacent
  infer_instance

/-- Generic chain family parametrized by an adjacency relation on archetypes. -/
def BridgeChainOf (adj : ArchetypeNode → ArchetypeNode → Prop) [DecidableRel adj] (n : Nat) : Type :=
  { t : Fin (n + 1) → ArchetypeNode // ∀ i : Fin n, adj (t i.castSucc) (t i.succ) }

instance instDecidableBridgeChainWitness
    (adj : ArchetypeNode → ArchetypeNode → Prop) [DecidableRel adj]
    (n : Nat) (t : Fin (n + 1) → ArchetypeNode) :
    Decidable (∀ i : Fin n, adj (t i.castSucc) (t i.succ)) := by
  classical
  infer_instance

instance instFintypeBridgeChainOf
    (adj : ArchetypeNode → ArchetypeNode → Prop) [DecidableRel adj]
    (n : Nat) : Fintype (BridgeChainOf adj n) := by
  classical
  unfold BridgeChainOf
  infer_instance

/-- Concrete bridge-chain family for the declared archetype network. -/
abbrev BridgeChain (n : Nat) : Type := BridgeChainOf bridgeAdjacent n

/-- Degree-`n` chain rank for a given adjacency relation. -/
def bridgeChainRankOf (adj : ArchetypeNode → ArchetypeNode → Prop) [DecidableRel adj] (n : Nat) : Nat :=
  Fintype.card (BridgeChainOf adj n)

/-- Degree-`n` chain rank for the declared bridge network. -/
abbrev bridgeChainRank (n : Nat) : Nat := bridgeChainRankOf bridgeAdjacent n

/-- Euler cut for a given adjacency relation on archetypes. -/
def bridgeEulerCutOf (adj : ArchetypeNode → ArchetypeNode → Prop) [DecidableRel adj] (N : Nat) : Int :=
  Finset.sum (Finset.range (N + 1))
    (fun n => ((-1 : Int) ^ n) * Int.ofNat (bridgeChainRankOf adj n))

/-- Euler cut for the declared bridge network. -/
abbrev bridgeEulerCut (N : Nat) : Int := bridgeEulerCutOf bridgeAdjacent N

/-- Degree-0 bridge chains are equivalent to archetype nodes. -/
def bridgeChainZeroEquivNode
    (adj : ArchetypeNode → ArchetypeNode → Prop) [DecidableRel adj] :
    BridgeChainOf adj 0 ≃ ArchetypeNode where
  toFun := fun x => x.1 0
  invFun := fun a => ⟨fun _ => a, by
    intro i
    exact Fin.elim0 i⟩
  left_inv := by
    intro x
    apply Subtype.ext
    funext i
    have hi : i = 0 := Fin.eq_zero i
    simp [hi]
  right_inv := by
    intro a
    rfl

theorem archetypeNode_count : Fintype.card ArchetypeNode = 17 := by
  decide

/-- The network degree-0 rank is the archetype object count. -/
theorem bridgeChainRank_zero_eq_nodeCount :
    bridgeChainRank 0 = 17 := by
  calc
    bridgeChainRank 0
        = Fintype.card ArchetypeNode := by
            simpa [bridgeChainRank, bridgeChainRankOf] using
              (Fintype.card_congr (bridgeChainZeroEquivNode (adj := bridgeAdjacent)))
    _ = 17 := archetypeNode_count

/-- The degree-0 bridge chain rank matches degree-0 magnitude chain rank. -/
theorem bridgeChainRank_zero_eq_magnitudeChainRank_zero :
    bridgeChainRank 0 = Metrics.Magnitude.chainRank ArchetypeNode 0 := by
  rw [bridgeChainRank_zero_eq_nodeCount,
      Metrics.Magnitude.chainRank_zero_eq_finiteMagnitude,
      Metrics.Magnitude.finiteMagnitude]
  exact archetypeNode_count

/-- The first Euler cut of the archetype network equals object cardinality. -/
theorem bridgeEulerCut_zero_eq_nodeCount :
    bridgeEulerCut 0 = 17 := by
  simp [bridgeEulerCut, bridgeEulerCutOf, bridgeChainRank_zero_eq_nodeCount]

/-- Build a degree-1 chain witness from any declared directed bridge. -/
def chainOneOfDirectedBridge {a b : ArchetypeNode} (h : hasDirectedBridge a b) : BridgeChain 1 :=
  ⟨fun i => if i = 0 then a else b, by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst hi
    simp [bridgeAdjacent, h]⟩

/-- Add a directed bridge candidate to an adjacency relation. -/
def insertDirectedBridge
    (adj : ArchetypeNode → ArchetypeNode → Prop)
    (u v : ArchetypeNode) :
    ArchetypeNode → ArchetypeNode → Prop :=
  fun a b => adj a b ∨ (a = u ∧ b = v)

instance instDecidableRelInsertDirectedBridge
    (adj : ArchetypeNode → ArchetypeNode → Prop) [DecidableRel adj]
    (u v : ArchetypeNode) :
    DecidableRel (insertDirectedBridge adj u v) := by
  intro a b
  unfold insertDirectedBridge
  infer_instance

/-- If an inserted edge already exists, insertion leaves adjacency unchanged. -/
theorem insertDirectedBridge_eq_of_present
    (u v : ArchetypeNode) (h : hasDirectedBridge u v) :
    insertDirectedBridge hasDirectedBridge u v = hasDirectedBridge := by
  funext a
  funext b
  apply propext
  constructor
  · intro hab
    rcases hab with hab | hab
    · exact hab
    · rcases hab with ⟨hau, hbv⟩
      subst hau
      subst hbv
      exact h
  · intro hab
    exact Or.inl hab

/-- Chain-rank invariance under extensional equality of adjacency relations. -/
theorem bridgeChainRankOf_congr
    (adj₁ adj₂ : ArchetypeNode → ArchetypeNode → Prop)
    [DecidableRel adj₁] [DecidableRel adj₂]
    (h : ∀ a b, adj₁ a b ↔ adj₂ a b) (n : Nat) :
    bridgeChainRankOf adj₁ n = bridgeChainRankOf adj₂ n := by
  let e : BridgeChainOf adj₁ n ≃ BridgeChainOf adj₂ n :=
    { toFun := fun x =>
        ⟨x.1, by
          intro i
          exact (h _ _).1 (x.2 i)⟩
      invFun := fun x =>
        ⟨x.1, by
          intro i
          exact (h _ _).2 (x.2 i)⟩
      left_inv := by
        intro x
        rfl
      right_inv := by
        intro x
        rfl }
  simpa [bridgeChainRankOf] using Fintype.card_congr e

/-- Euler-cut invariance under extensional equality of adjacency relations. -/
theorem bridgeEulerCutOf_congr
    (adj₁ adj₂ : ArchetypeNode → ArchetypeNode → Prop)
    [DecidableRel adj₁] [DecidableRel adj₂]
    (h : ∀ a b, adj₁ a b ↔ adj₂ a b) (N : Nat) :
    bridgeEulerCutOf adj₁ N = bridgeEulerCutOf adj₂ N := by
  unfold bridgeEulerCutOf
  refine Finset.sum_congr rfl ?_
  intro n hn
  simp [bridgeChainRankOf_congr (adj₁ := adj₁) (adj₂ := adj₂) h n]

/-- Redundant insertion (already-present edge) preserves every bridge-chain rank. -/
theorem redundant_insertion_preserves_chainRank
    (u v : ArchetypeNode) (h : hasDirectedBridge u v) (n : Nat) :
    bridgeChainRankOf (insertDirectedBridge bridgeAdjacent u v) n = bridgeChainRank n := by
  have huvadj : bridgeAdjacent u v := Or.inl h
  have hadd :
      ∀ a b,
        insertDirectedBridge bridgeAdjacent u v a b ↔ bridgeAdjacent a b := by
    intro a b
    constructor
    · intro hab
      rcases hab with hab | hab
      · exact hab
      · rcases hab with ⟨hau, hbv⟩
        subst hau
        subst hbv
        exact huvadj
    · intro hab
      exact Or.inl hab
  simpa [bridgeChainRank] using
    bridgeChainRankOf_congr (adj₁ := insertDirectedBridge bridgeAdjacent u v)
      (adj₂ := bridgeAdjacent) hadd n

/-- Redundant insertion (already-present edge) preserves the Euler-cut metric. -/
theorem redundant_insertion_preserves_eulerCut
    (u v : ArchetypeNode) (h : hasDirectedBridge u v) (N : Nat) :
    bridgeEulerCutOf (insertDirectedBridge bridgeAdjacent u v) N = bridgeEulerCut N := by
  have huvadj : bridgeAdjacent u v := Or.inl h
  have hadd :
      ∀ a b,
        insertDirectedBridge bridgeAdjacent u v a b ↔ bridgeAdjacent a b := by
    intro a b
    constructor
    · intro hab
      rcases hab with hab | hab
      · exact hab
      · rcases hab with ⟨hau, hbv⟩
        subst hau
        subst hbv
        exact huvadj
    · intro hab
      exact Or.inl hab
  simpa [bridgeEulerCut] using
    bridgeEulerCutOf_congr (adj₁ := insertDirectedBridge bridgeAdjacent u v)
      (adj₂ := bridgeAdjacent) hadd N

/-- Adding a genuinely new directed adjacency can increase degree-1 chain rank. -/
theorem new_edge_may_change_chainRank_one
    (u v : ArchetypeNode) (hnotadj : ¬ bridgeAdjacent u v) (_huv : u ≠ v) :
    bridgeChainRankOf (insertDirectedBridge bridgeAdjacent u v) 1 >
      bridgeChainRank 1 := by
  let oldT := BridgeChainOf bridgeAdjacent 1
  let newT := BridgeChainOf (insertDirectedBridge bridgeAdjacent u v) 1
  let emb : oldT ↪ newT :=
    { toFun := fun x =>
        ⟨x.1, by
          intro i
          exact Or.inl (x.2 i)⟩
      inj' := by
        intro x y hxy
        cases x
        cases y
        cases hxy
        rfl }
  have hNotSurj : ¬ Function.Surjective emb := by
    intro hsurj
    let y : newT := by
      refine ⟨(fun i => if i = 0 then u else v), ?_⟩
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst hi
      right
      exact ⟨by simp, by simp⟩
    rcases hsurj y with ⟨x, hx⟩
    have hOldOnEmb : bridgeAdjacent ((emb x).1 0) ((emb x).1 1) := by
      simpa using x.2 0
    have hOldOnY : bridgeAdjacent (y.1 0) (y.1 1) := by
      simpa [hx] using hOldOnEmb
    have huvAdj : bridgeAdjacent u v := by
      simpa [y] using hOldOnY
    exact hnotadj huvAdj
  have hlt : Fintype.card oldT < Fintype.card newT :=
    Fintype.card_lt_of_injective_not_surjective emb emb.injective hNotSurj
  simpa [bridgeChainRank, bridgeChainRankOf, oldT, newT] using hlt

/-- The uniform weighting on archetypes solves the discrete weighting equations. -/
theorem archetype_uniform_weighting :
    Metrics.Magnitude.IsMagnitudeWeighting
      (Metrics.Magnitude.discreteSimilarity ArchetypeNode)
      (Metrics.Magnitude.uniformWeighting ArchetypeNode) :=
  Metrics.Magnitude.uniformWeighting_is_discrete_weighting ArchetypeNode

/-- The archetype network discrete magnitude is exactly `17`. -/
theorem archetype_magnitude_eq_17 :
    Metrics.Magnitude.magnitudeOfWeighting
      (Metrics.Magnitude.uniformWeighting ArchetypeNode) = 17 := by
  simpa [archetypeNode_count] using
    (Metrics.Magnitude.magnitudeOfWeighting_uniform ArchetypeNode)

/-- An eventually-stable archetype ratchet converges in the paged chain-complex model. -/
theorem archetype_ratchet_converges :
    Algebra.SpectralSequence.PageConverges
      (Algebra.SpectralSequence.pagedOfRatchetAndComplex
        (Metrics.Magnitude.magnitudeChainComplex ArchetypeNode)
        (fun n => Nat.min n 17)
        (by
          intro a b hab
          exact min_le_min_right 17 hab))
      17 := by
  refine Algebra.SpectralSequence.pagedConverges_of_stabilizes
    (C := Metrics.Magnitude.magnitudeChainComplex ArchetypeNode)
    (level := fun n => Nat.min n 17)
    (htraj := by
      intro a b hab
      exact min_le_min_right 17 hab)
    (N := 17) ?_
  intro n hn
  have h17 : Nat.min n 17 = 17 := Nat.min_eq_right hn
  simp [h17]

end Archetype
end Bridges
end HeytingLean
