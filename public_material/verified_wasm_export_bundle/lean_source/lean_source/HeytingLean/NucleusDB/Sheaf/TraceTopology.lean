import HeytingLean.Metrics.Magnitude.BlurredPersistent
import Mathlib.Logic.Relation
import Mathlib.Tactic.FinCases

/-!
# NucleusDB.Sheaf.TraceTopology

A first formal bridge from AgentHALO trace-topology data to the existing
magnitude-chain infrastructure.

This module is intentionally partial. It does **not** claim a full magnitude
homology theorem. Instead it packages the pieces that are already honest and
useful:

- a finite tool-metric surface for execution traces,
- threshold neighborhood graphs and their reachability relation,
- a quotient of tools by threshold-connectedness,
- monotonicity of connectivity and component counts as the threshold grows or
  the trace metric is refined,
- the universal property that any trace observable constant on connected
  components factors through that quotient, and
- a concrete bridge between degree-1 Vietoris-Rips simplices and trace-graph
  edges.

The ambient magnitude infrastructure is still pseudometric-level: we assume
reflexivity and symmetry of the distance, but not a triangle inequality. That
limitation is inherited from the existing `MetricMagnitudeSpace` surface rather
than introduced here.

The remaining gap to a full mathematical WP-8 closure is the chain-level `H0`
/ magnitude-homology comparison, not the metric, quotient, or persistence
scaffolding already used by runtime trace analysis.
-/

namespace HeytingLean
namespace NucleusDB
namespace Sheaf
namespace TraceTopology

universe u

open Relation

/-- Finite metric surface on a tool alphabet, used to model execution traces. -/
structure ToolMetricSpace (α : Type u) extends Fintype α where
  decEq : DecidableEq α
  dist : α → α → Nat
  dist_self : ∀ x, dist x x = 0
  dist_symm : ∀ x y, dist x y = dist y x

attribute [instance] ToolMetricSpace.decEq

instance {α : Type u} (M : ToolMetricSpace α) : Fintype α := M.toFintype

/-- Reuse the existing magnitude-chain infrastructure on a trace metric. -/
def toMetricMagnitudeSpace {α : Type u} (M : ToolMetricSpace α) :
    HeytingLean.Metrics.Magnitude.MetricMagnitudeSpace α where
  toFintype := M.toFintype
  decEq := M.decEq
  dist := M.dist
  dist_self := M.dist_self
  dist_symm := M.dist_symm

/-- Vietoris-Rips simplices for the trace metric, reusing the magnitude layer. -/
abbrev VRSimplex {α : Type u} (M : ToolMetricSpace α) (n t : Nat) : Type u :=
  @HeytingLean.Metrics.Magnitude.VRChain α (toMetricMagnitudeSpace M) n t

/-- The threshold neighborhood graph on tools. -/
def Neighbor {α : Type u} (M : ToolMetricSpace α) (t : Nat) : α → α → Prop :=
  fun x y => M.dist x y ≤ t

/-- Reachability in the threshold neighborhood graph. -/
abbrev Connected {α : Type u} (M : ToolMetricSpace α) (t : Nat) : α → α → Prop :=
  ReflTransGen (Neighbor M t)

/-- A refined trace metric only decreases distances, hence only adds edges. -/
def Refines {α : Type u} (M N : ToolMetricSpace α) : Prop :=
  ∀ x y, N.dist x y ≤ M.dist x y

@[simp] theorem neighbor_refl {α : Type u} (M : ToolMetricSpace α) (t : Nat) (x : α) :
    Neighbor M t x x := by
  simp [Neighbor, M.dist_self]

theorem neighbor_symm {α : Type u} (M : ToolMetricSpace α) (t : Nat) {x y : α} :
    Neighbor M t x y → Neighbor M t y x := by
  intro h
  simp [Neighbor, M.dist_symm] at h ⊢
  exact h

theorem connected_symm {α : Type u} (M : ToolMetricSpace α) (t : Nat) {x y : α} :
    Connected M t x y → Connected M t y x := by
  have hsymm : Symmetric (Neighbor M t) := fun _ _ => neighbor_symm M t
  intro h
  exact Relation.ReflTransGen.symmetric hsymm h

theorem connected_is_equivalence {α : Type u} (M : ToolMetricSpace α) (t : Nat) :
    Equivalence (Connected M t) :=
  ⟨Relation.reflexive_reflTransGen, connected_symm M t, ReflTransGen.trans⟩

/-- The setoid of threshold-connected tools. -/
def connectedSetoid {α : Type u} (M : ToolMetricSpace α) (t : Nat) : Setoid α :=
  Setoid.mk _ (connected_is_equivalence M t)

/-- Connected components of the threshold-neighborhood graph. -/
abbrev ConnectedComponent {α : Type u} (M : ToolMetricSpace α) (t : Nat) : Type u :=
  Quotient (connectedSetoid M t)

noncomputable instance instDecidableRelConnected {α : Type u}
    (M : ToolMetricSpace α) (t : Nat) : DecidableRel (Connected M t) :=
  Classical.decRel _

noncomputable instance instFintypeConnectedComponent {α : Type u}
    (M : ToolMetricSpace α) (t : Nat) : Fintype (ConnectedComponent M t) := by
  classical
  exact @Quotient.fintype α M.toFintype (connectedSetoid M t) (instDecidableRelConnected M t)

/-- Runtime-facing count of threshold-connected trace components. This is the
operational `H0` surrogate used by trace analysis even before a full chain-level
homology identification theorem is available. -/
noncomputable def componentCount {α : Type u} (M : ToolMetricSpace α) (t : Nat) : Nat :=
  Fintype.card (ConnectedComponent M t)

/-- An observable is component-constant when it agrees on every threshold-connected pair. -/
def ComponentConstant {α : Type u} (M : ToolMetricSpace α) (t : Nat) {β : Type*}
    (f : α → β) : Prop :=
  ∀ ⦃x y : α⦄, Connected M t x y → f x = f y

noncomputable instance instDecidableComponentConstant {α : Type u}
    (M : ToolMetricSpace α) (t : Nat) {β : Type*} (f : α → β) :
    Decidable (ComponentConstant M t f) := by
  classical
  infer_instance

/-- Component-constant observables factor through the connected-component quotient. -/
def liftConnectedComponent {α : Type u} (M : ToolMetricSpace α) (t : Nat) {β : Type*}
    (f : α → β) (hf : ComponentConstant M t f) :
    ConnectedComponent M t → β :=
  Quotient.lift f (by
    intro x y hxy
    exact hf hxy)

@[simp] theorem liftConnectedComponent_mk {α : Type u} (M : ToolMetricSpace α) (t : Nat)
    {β : Type*} (f : α → β) (hf : ComponentConstant M t f) (x : α) :
    liftConnectedComponent M t f hf (Quotient.mk'' x) = f x := by
  rfl

/-- The connected-component quotient has the expected universal property. -/
theorem componentConstant_iff_exists_lift {α : Type u} (M : ToolMetricSpace α) (t : Nat)
    {β : Type*} (f : α → β) :
    ComponentConstant M t f ↔
      ∃ g : ConnectedComponent M t → β, ∀ x : α, g (Quotient.mk'' x) = f x := by
  constructor
  · intro hf
    refine ⟨liftConnectedComponent M t f hf, ?_⟩
    intro x
    simp [liftConnectedComponent_mk]
  · rintro ⟨g, hg⟩ x y hxy
    have hx : g (Quotient.mk'' x) = f x := hg x
    have hy : g (Quotient.mk'' y) = f y := hg y
    have hq : (Quotient.mk'' x : ConnectedComponent M t) = Quotient.mk'' y :=
      Quotient.sound hxy
    calc
      f x = g (Quotient.mk'' x) := hx.symm
      _ = g (Quotient.mk'' y) := by simp [hq]
      _ = f y := hy

/-- The quotient lift is unique among functions that agree on representatives. -/
theorem liftConnectedComponent_unique {α : Type u} (M : ToolMetricSpace α) (t : Nat)
    {β : Type*} (f : α → β) (hf : ComponentConstant M t f)
    (g : ConnectedComponent M t → β)
    (hg : ∀ x : α, g (Quotient.mk'' x) = f x) :
    g = liftConnectedComponent M t f hf := by
  funext q
  refine Quotient.inductionOn q ?_
  intro x
  simpa [liftConnectedComponent_mk] using hg x

/-- Increasing the threshold only adds neighborhood edges. -/
theorem neighbor_mono_of_scale {α : Type u} (M : ToolMetricSpace α) {s t : Nat}
    (hst : s ≤ t) {x y : α} :
    Neighbor M s x y → Neighbor M t x y := by
  exact fun h => le_trans h hst

/-- Metric refinement preserves threshold edges. -/
theorem refines_preserves_neighbor {α : Type u} {M N : ToolMetricSpace α}
    (href : Refines M N) {t : Nat} {x y : α} :
    Neighbor M t x y → Neighbor N t x y := by
  intro hxy
  exact le_trans (href x y) hxy

/-- Threshold reachability is monotone in the scale parameter. -/
theorem connected_mono_of_scale {α : Type u} (M : ToolMetricSpace α) {s t : Nat}
    (hst : s ≤ t) {x y : α} :
    Connected M s x y → Connected M t x y := by
  intro hxy
  induction hxy using Relation.ReflTransGen.trans_induction_on with
  | refl x =>
      exact ReflTransGen.refl
  | single hstep =>
      exact ReflTransGen.single (neighbor_mono_of_scale M hst hstep)
  | trans _ _ ihab ihbc =>
      exact ReflTransGen.trans ihab ihbc

/-- Metric refinement preserves threshold reachability. -/
theorem refines_preserves_connected {α : Type u} {M N : ToolMetricSpace α}
    (href : Refines M N) {t : Nat} {x y : α} :
    Connected M t x y → Connected N t x y := by
  intro hxy
  induction hxy using Relation.ReflTransGen.trans_induction_on with
  | refl x =>
      exact ReflTransGen.refl
  | single hstep =>
      exact ReflTransGen.single (refines_preserves_neighbor href hstep)
  | trans _ _ ihab ihbc =>
      exact ReflTransGen.trans ihab ihbc

/-- The identity on tools descends to connected components as the threshold grows. -/
def connectedComponentMapOfScale {α : Type u} (M : ToolMetricSpace α) {s t : Nat}
    (hst : s ≤ t) :
    ConnectedComponent M s → ConnectedComponent M t :=
  Quotient.map' id (fun _ _ hxy => connected_mono_of_scale M hst hxy)

theorem connectedComponentMapOfScale_surjective {α : Type u} (M : ToolMetricSpace α)
    {s t : Nat} (hst : s ≤ t) :
    Function.Surjective (connectedComponentMapOfScale M hst) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  exact ⟨Quotient.mk'' x, rfl⟩

/-- The identity on tools also descends to connected components under metric refinement. -/
def connectedComponentMapOfRefines {α : Type u} {M N : ToolMetricSpace α}
    (href : Refines M N) {t : Nat} :
    ConnectedComponent M t → ConnectedComponent N t :=
  Quotient.map' id (fun _ _ hxy => refines_preserves_connected href hxy)

theorem connectedComponentMapOfRefines_surjective {α : Type u}
    {M N : ToolMetricSpace α} (href : Refines M N) {t : Nat} :
    Function.Surjective (connectedComponentMapOfRefines href (t := t)) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  exact ⟨Quotient.mk'' x, rfl⟩

/-- Threshold monotonicity for VR simplices on the same tool metric. -/
def vrSimplex_mono_of_scale {α : Type u} (M : ToolMetricSpace α) {n s t : Nat}
    (hst : s ≤ t) :
    VRSimplex M n s → VRSimplex M n t
  | ⟨τ, hτ⟩ => ⟨τ, fun i j => le_trans (hτ i j) hst⟩

/-- Metric refinement preserves all existing VR simplices at a fixed threshold. -/
def vrSimplex_mono_of_refines {α : Type u} {M N : ToolMetricSpace α}
    (href : Refines M N) {n t : Nat} :
    VRSimplex M n t → VRSimplex N n t
  | ⟨τ, hτ⟩ => ⟨τ, fun i j => le_trans (href _ _) (hτ i j)⟩

/-- Degree-0 VR simplices are exactly the underlying tool alphabet. -/
def vrDegreeZeroEquiv {α : Type u} (M : ToolMetricSpace α) (t : Nat) :
    VRSimplex M 0 t ≃ α where
  toFun := fun τ => τ.1.1 0
  invFun := fun x =>
    ⟨⟨fun _ => x, by
      intro i
      exact Fin.elim0 i⟩, by
      intro i j
      have hi : i = 0 := Fin.eq_zero i
      have hj : j = 0 := Fin.eq_zero j
      subst hi
      subst hj
      simp [toMetricMagnitudeSpace, M.dist_self]⟩
  left_inv := by
    intro τ
    apply Subtype.ext
    apply Subtype.ext
    funext i
    fin_cases i
    rfl
  right_inv := by
    intro x
    rfl

/-- Carrier cardinality of a finite tool metric surface. -/
def carrierCard {α : Type u} (M : ToolMetricSpace α) : Nat :=
  @Fintype.card α M.toFintype

/-- Degree-0 VR rank depends only on the carrier cardinality. -/
theorem card_vr_degreeZero {α : Type u} (M : ToolMetricSpace α) (t : Nat) :
    Fintype.card (VRSimplex M 0 t) = carrierCard M := by
  exact @Fintype.card_congr (VRSimplex M 0 t) α inferInstance M.toFintype (vrDegreeZeroEquiv M t)

/-- Connected components are a quotient of the carrier, so there are never more
components than degree-0 VR generators. -/
theorem card_connectedComponent_le_degreeZero_rank {α : Type u}
    (M : ToolMetricSpace α) (t : Nat) :
    Fintype.card (ConnectedComponent M t) ≤ Fintype.card (VRSimplex M 0 t) := by
  classical
  calc
    Fintype.card (ConnectedComponent M t) ≤ carrierCard M := by
      simpa [ConnectedComponent, connectedSetoid, carrierCard] using
        (@Fintype.card_le_of_surjective α (ConnectedComponent M t)
          M.toFintype (instFintypeConnectedComponent M t)
          (Quotient.mk'' : α → ConnectedComponent M t)
          Quotient.mk''_surjective)
    _ = Fintype.card (VRSimplex M 0 t) := by
      symm
      exact card_vr_degreeZero M t

theorem componentCount_le_degreeZero_rank {α : Type u}
    (M : ToolMetricSpace α) (t : Nat) :
    componentCount M t ≤ Fintype.card (VRSimplex M 0 t) := by
  simpa [componentCount] using card_connectedComponent_le_degreeZero_rank M t

/-- Trace refinement preserves the degree-0 VR rank exactly.
This is a degree-0 chain-rank statement, not yet the full `H0` quotient theorem. -/
theorem refines_preserves_degreeZero_rank {α : Type u} {M N : ToolMetricSpace α}
    (_href : Refines M N) (t : Nat) :
    Fintype.card (VRSimplex M 0 t) = Fintype.card (VRSimplex N 0 t) := by
  rw [card_vr_degreeZero, card_vr_degreeZero]
  simpa [carrierCard] using (@Fintype.card_congr α α M.toFintype N.toFintype (Equiv.refl α))

/-- Increasing the threshold can only merge connected components. -/
theorem card_connectedComponent_mono_of_scale {α : Type u} (M : ToolMetricSpace α)
    {s t : Nat} (hst : s ≤ t) :
    Fintype.card (ConnectedComponent M t) ≤ Fintype.card (ConnectedComponent M s) := by
  classical
  exact Fintype.card_le_of_surjective _ (connectedComponentMapOfScale_surjective M hst)

theorem componentCount_mono_of_scale {α : Type u} (M : ToolMetricSpace α)
    {s t : Nat} (hst : s ≤ t) :
    componentCount M t ≤ componentCount M s := by
  simpa [componentCount] using card_connectedComponent_mono_of_scale M hst

/-- Refining the metric can only merge connected components. -/
theorem card_connectedComponent_mono_of_refines {α : Type u}
    {M N : ToolMetricSpace α} (href : Refines M N) {t : Nat} :
    Fintype.card (ConnectedComponent N t) ≤ Fintype.card (ConnectedComponent M t) := by
  classical
  exact Fintype.card_le_of_surjective _ (connectedComponentMapOfRefines_surjective href)

theorem componentCount_mono_of_refines {α : Type u}
    {M N : ToolMetricSpace α} (href : Refines M N) {t : Nat} :
    componentCount N t ≤ componentCount M t := by
  simpa [componentCount] using card_connectedComponent_mono_of_refines href (t := t)

/-- Canonical degree-1 chain joining two distinct tools. -/
def edgeChain {α : Type u} (M : ToolMetricSpace α) {x y : α} (hxy : x ≠ y) :
    @HeytingLean.Metrics.Magnitude.MagnitudeChain α M.decEq 1 :=
  ⟨fun
    | 0 => x
    | 1 => y,
    by
      intro i
      fin_cases i
      simpa using hxy⟩

/-- Any threshold edge yields a degree-1 VR simplex. -/
def edgeToVRSimplex {α : Type u} (M : ToolMetricSpace α) {x y : α}
    (hxy : x ≠ y) {t : Nat} (hEdge : Neighbor M t x y) :
    VRSimplex M 1 t :=
  ⟨edgeChain M hxy, by
    have hEdge' : M.dist y x ≤ t := by
      simpa [Neighbor, M.dist_symm] using hEdge
    intro i j
    fin_cases i <;> fin_cases j
    · simp [toMetricMagnitudeSpace, M.dist_self]
    · simpa [Neighbor] using hEdge
    · simpa using hEdge'
    · simp [toMetricMagnitudeSpace, M.dist_self]⟩

/-- Reading off the two endpoints of a degree-1 VR simplex yields a threshold edge. -/
theorem vrSimplex_degreeOne_edge {α : Type u} (M : ToolMetricSpace α) {t : Nat}
    (τ : VRSimplex M 1 t) :
    Neighbor M t (τ.1.1 0) (τ.1.1 1) := by
  simpa [Neighbor] using τ.2 (0 : Fin 2) (1 : Fin 2)

/-- Degree-1 VR witnesses are equivalent to neighborhood edges with chosen endpoints. -/
theorem neighbor_iff_nonempty_vrDegreeOne {α : Type u} (M : ToolMetricSpace α)
    {x y : α} (hxy : x ≠ y) {t : Nat} :
    Neighbor M t x y ↔
      Nonempty {τ : VRSimplex M 1 t // τ.1.1 0 = x ∧ τ.1.1 1 = y} := by
  constructor
  · intro hEdge
    refine ⟨⟨edgeToVRSimplex M hxy hEdge, ?_⟩⟩
    constructor <;> rfl
  · rintro ⟨⟨τ, h0, h1⟩⟩
    simpa [h0, h1] using vrSimplex_degreeOne_edge M τ

end TraceTopology
end Sheaf
end NucleusDB
end HeytingLean
