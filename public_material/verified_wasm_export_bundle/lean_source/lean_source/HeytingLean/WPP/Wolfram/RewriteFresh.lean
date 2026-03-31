import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.Nodup
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Multiset.AddSub
import HeytingLean.WPP.Wolfram.FreshSupply
import HeytingLean.WPP.Wolfram.Hypergraph

namespace HeytingLean
namespace WPP
namespace Wolfram

/-!
# Rewrite semantics with fresh vertices (SetReplace-style)

This extends the basic `Rewrite` layer with an explicit account of **fresh** vertices:
the RHS of a rule may mention vertices not bound by the LHS match, and those are instantiated
using a `FreshSupply` so they do not collide with vertices already present in the state.

The key correctness statement is an **α-equivalence** lemma: any two fresh choices (disjoint
from the current state's vertices and injective) lead to states that are isomorphic by a
vertex relabeling that fixes the old vertices.
-/

universe u v

/-- A rule schema over pattern vertices `P`, with `nFresh` fresh placeholders. -/
structure RuleFresh (P : Type u) where
  nFresh : Nat
  lhs : HGraph P
  rhs : HGraph (Sum P (Fin nFresh))

namespace RuleFresh

@[simp] def instLhs {P : Type u} {V : Type v} (r : RuleFresh P) (σ : P → V) : HGraph V :=
  HGraph.rename σ r.lhs

@[simp] def instRhs {P : Type u} {V : Type v} (r : RuleFresh P) (σ : P → V) (τ : Fin r.nFresh → V) :
    HGraph V :=
  HGraph.rename (Sum.elim σ τ) r.rhs

/-- A Wolfram rule is *well-formed* if every `P`-vertex used on the RHS is also used on the LHS. -/
def WellFormed {P : Type u} (r : RuleFresh P) : Prop :=
  ∀ p : P, (∃ e ∈ r.rhs, (Sum.inl p) ∈ e) → (∃ e ∈ r.lhs, p ∈ e)

end RuleFresh

/-- A Wolfram-model system with fresh-vertex rules (SetReplace-style). -/
structure SystemFresh (V : Type u) (P : Type v) where
  rules : List (RuleFresh P)
  init : HGraph V

namespace SystemFresh

variable {V : Type u} {P : Type v} (sys : SystemFresh V P)

/-- An event chooses a rule index and a match-substitution for its `P`-variables. -/
structure Event (sys : SystemFresh V P) where
  idx : Fin sys.rules.length
  σ : P → V

namespace Event

variable {sys : SystemFresh V P}

@[simp] def rule (e : sys.Event) : RuleFresh P :=
  sys.rules.get e.idx

/-- The instantiated LHS destroyed by this event. -/
@[simp] def input (e : sys.Event) : HGraph V :=
  (e.rule).instLhs e.σ

/-- A freshness predicate for an explicit fresh assignment `τ`. -/
def FreshAssign [DecidableEq V] (e : sys.Event) (τ : Fin (e.rule.nFresh) → V) (s : HGraph V) : Prop :=
  Function.Injective τ ∧ ∀ i, τ i ∉ HGraph.verts (V := V) s

instance [DecidableEq V] (e : sys.Event) (τ : Fin (e.rule.nFresh) → V) (s : HGraph V) :
    Decidable (e.FreshAssign τ s) := by
  classical
  dsimp [FreshAssign]
  infer_instance

/-- Applicability: inputs are available as a submultiset of the current state. -/
def Applicable (e : sys.Event) (s : HGraph V) : Prop :=
  e.input ≤ s

instance decidableApplicable [DecidableEq V] (e : sys.Event) (s : HGraph V) :
    Decidable (e.Applicable s) := by
  dsimp [Applicable]
  infer_instance

variable [DecidableEq V]

/-- Apply the event with an *explicit* fresh assignment. -/
def applyWith (e : sys.Event) (τ : Fin (e.rule.nFresh) → V) (s : HGraph V) : HGraph V :=
  s - e.input + (e.rule).instRhs e.σ τ

/-- Apply the event using a `FreshSupply`, allocating fresh vertices from the current state's support. -/
noncomputable def apply (e : sys.Event) [FreshSupply V] (s : HGraph V) : HGraph V :=
  e.applyWith (FreshSupply.alloc (V := V) (e.rule.nFresh) (HGraph.verts (V := V) s)) s

/-- Fresh-supply allocation satisfies `FreshAssign`. -/
lemma freshAssign_alloc [FreshSupply V] (e : sys.Event) (s : HGraph V) :
    e.FreshAssign (FreshSupply.alloc (V := V) (e.rule.nFresh) (HGraph.verts (V := V) s)) s := by
  refine ⟨FreshSupply.alloc_injective (V := V) _ _, ?_⟩
  intro i
  exact FreshSupply.alloc_not_mem (V := V) _ _ i

/-- Helper: range of an assignment `Fin n → V` as a finset. -/
def rangeFinset {n : Nat} (τ : Fin n → V) : Finset V :=
  (Finset.univ : Finset (Fin n)).image τ

lemma mem_rangeFinset {n : Nat} (τ : Fin n → V) (i : Fin n) : τ i ∈ rangeFinset (V := V) τ := by
  classical
  refine Finset.mem_image.2 ?_
  exact ⟨i, by simp, rfl⟩

/-- Cross-disjointness: the ranges of `τ₁` and `τ₂` do not overlap pointwise. -/
def CrossDisjoint {n : Nat} (τ₁ τ₂ : Fin n → V) : Prop :=
  ∀ i j, τ₁ i ≠ τ₂ j

lemma crossDisjoint_of_not_mem_range {n : Nat} {τ₁ τ₂ : Fin n → V}
    (h : ∀ j, τ₂ j ∉ rangeFinset (V := V) τ₁) : CrossDisjoint (V := V) τ₁ τ₂ := by
  intro i j hij
  have : τ₂ j ∈ rangeFinset (V := V) τ₁ := by
    simpa [hij] using mem_rangeFinset (V := V) τ₁ i
  exact (h j this).elim

/-- Swap two disjoint fresh assignments componentwise, as a permutation of `V`. -/
def swapPerm : ∀ {n : Nat}, (Fin n → V) → (Fin n → V) → Equiv.Perm V
  | 0, _τ₁, _τ₂ => Equiv.refl V
  | n + 1, τ₁, τ₂ =>
      (Equiv.swap (τ₁ 0) (τ₂ 0)).trans <|
        swapPerm (n := n) (fun i => τ₁ i.succ) (fun i => τ₂ i.succ)

lemma swapPerm_apply_of_forall_ne {n : Nat} {τ₁ τ₂ : Fin n → V} {x : V}
    (h₁ : ∀ i, x ≠ τ₁ i) (h₂ : ∀ i, x ≠ τ₂ i) :
    swapPerm τ₁ τ₂ x = x := by
  induction n generalizing x with
  | zero =>
      simp [swapPerm]
  | succ n ih =>
      have h₁' : ∀ i : Fin n, x ≠ τ₁ i.succ := fun i => h₁ i.succ
      have h₂' : ∀ i : Fin n, x ≠ τ₂ i.succ := fun i => h₂ i.succ
      have hxRest :
          swapPerm (fun i => τ₁ i.succ) (fun i => τ₂ i.succ) x = x :=
        ih (τ₁ := fun i => τ₁ i.succ) (τ₂ := fun i => τ₂ i.succ) (x := x) h₁' h₂'
      have hx0 : x ≠ τ₁ 0 := h₁ 0
      have hx1 : x ≠ τ₂ 0 := h₂ 0
      simp [swapPerm, Equiv.swap_apply_def, hxRest, hx0, hx1]

lemma swapPerm_apply_left {n : Nat} {τ₁ τ₂ : Fin n → V}
    (hτ₁ : Function.Injective τ₁) (hτ₂ : Function.Injective τ₂)
    (hdis : CrossDisjoint (V := V) τ₁ τ₂) (i : Fin n) :
    swapPerm τ₁ τ₂ (τ₁ i) = τ₂ i := by
  induction n with
  | zero =>
      exact (Fin.elim0 i)
  | succ n ih =>
      cases i using Fin.cases with
      | zero =>
          -- Show the tail-permutation fixes `τ₂ 0`.
          have h₁' : ∀ j : Fin n, τ₂ 0 ≠ τ₁ j.succ := by
            intro j hEq
            exact (hdis j.succ 0) hEq.symm
          have h₂' : ∀ j : Fin n, τ₂ 0 ≠ τ₂ j.succ := by
            intro j hEq
            have : (0 : Fin (n + 1)) = j.succ := hτ₂ hEq
            exact (Fin.succ_ne_zero j) this.symm
          have hrest :
              swapPerm (fun j => τ₁ j.succ) (fun j => τ₂ j.succ) (τ₂ 0) = τ₂ 0 :=
            swapPerm_apply_of_forall_ne (V := V) (τ₁ := fun j => τ₁ j.succ) (τ₂ := fun j => τ₂ j.succ)
              (x := τ₂ 0) h₁' h₂'
          -- Unfold `swapPerm` at `n+1` and simplify.
          simp [swapPerm, Equiv.trans_apply, hrest]
      | succ i =>
          have hτ₁' : Function.Injective (fun j : Fin n => τ₁ j.succ) := by
            intro a b hab
            have : (a.succ : Fin (n + 1)) = b.succ := hτ₁ hab
            exact Fin.succ_inj.mp this
          have hτ₂' : Function.Injective (fun j : Fin n => τ₂ j.succ) := by
            intro a b hab
            have : (a.succ : Fin (n + 1)) = b.succ := hτ₂ hab
            exact Fin.succ_inj.mp this
          have hdis' : CrossDisjoint (V := V) (fun j : Fin n => τ₁ j.succ) (fun j : Fin n => τ₂ j.succ) := by
            intro a b
            exact hdis a.succ b.succ
          have hrest :
              swapPerm (fun j : Fin n => τ₁ j.succ) (fun j : Fin n => τ₂ j.succ) (τ₁ i.succ) = τ₂ i.succ :=
            ih (τ₁ := fun j : Fin n => τ₁ j.succ) (τ₂ := fun j : Fin n => τ₂ j.succ) hτ₁' hτ₂' hdis' i
          have hne_a : τ₁ i.succ ≠ τ₁ 0 := by
            intro hEq
            have : (i.succ : Fin (n + 1)) = 0 := hτ₁ hEq
            exact (Fin.succ_ne_zero i) this
          have hne_b : τ₁ i.succ ≠ τ₂ 0 := by
            intro hEq
            exact (hdis i.succ 0) hEq
          have hswap : Equiv.swap (τ₁ 0) (τ₂ 0) (τ₁ i.succ) = τ₁ i.succ := by
            simp [Equiv.swap_apply_def, hne_a, hne_b]
          -- Since `τ₁ i.succ` is disjoint from the head swap, the head swap is the identity on it.
          simp [swapPerm, Equiv.trans_apply, hswap, hrest]

lemma swapPerm_fix_of_mem_verts {n : Nat} {τ₁ τ₂ : Fin n → V} {s : HGraph V}
    (hτ₁ : ∀ i, τ₁ i ∉ HGraph.verts (V := V) s)
    (hτ₂ : ∀ i, τ₂ i ∉ HGraph.verts (V := V) s)
    {x : V} (hx : x ∈ HGraph.verts (V := V) s) :
    swapPerm τ₁ τ₂ x = x := by
  refine swapPerm_apply_of_forall_ne (V := V) (τ₁ := τ₁) (τ₂ := τ₂) (x := x) ?_ ?_
  · intro i hEq
    exact (hτ₁ i) (hEq ▸ hx)
  · intro i hEq
    exact (hτ₂ i) (hEq ▸ hx)

omit [DecidableEq V] in
private lemma expr_rename_eq_self_of_forall_mem (f : V → V) (e : Expr V) (h : ∀ x ∈ e, f x = x) :
    Expr.rename f e = e := by
  induction e with
  | nil =>
      simp [Expr.rename]
  | cons a e ih =>
      have ha : f a = a := h a (by simp)
      have ht : ∀ x ∈ e, f x = x := by
        intro x hx
        exact h x (by simp [hx])
      have htail : Expr.rename f e = e := ih ht
      simpa [Expr.rename, ha] using congrArg (List.cons a) htail

omit [DecidableEq V] in
private lemma hgraph_rename_eq_self_of_forall_mem (f : V → V) (g : HGraph V)
    (h : ∀ e ∈ g, Expr.rename f e = e) : HGraph.rename f g = g := by
  classical
  induction g using Multiset.induction_on with
  | empty =>
      simp [HGraph.rename]
  | cons a s ih =>
      have ha : Expr.rename f a = a := h a (by simp)
      have hs : ∀ e ∈ s, Expr.rename f e = e := by
        intro e he
        exact h e (by simp [he])
      have htail : HGraph.rename f s = s := ih hs
      calc
        HGraph.rename f (a ::ₘ s) = Expr.rename f a ::ₘ HGraph.rename f s := by
          simp only [HGraph.rename, Multiset.map_cons]
        _ = a ::ₘ s := by
          rw [ha, htail]

private lemma hgraph_rename_eq_self_of_fix_verts (f : V → V) (s : HGraph V)
    (hfix : ∀ x ∈ HGraph.verts (V := V) s, f x = x) : HGraph.rename f s = s := by
  apply hgraph_rename_eq_self_of_forall_mem (V := V) (f := f) (g := s)
  intro e he
  apply expr_rename_eq_self_of_forall_mem (V := V) (f := f) (e := e)
  intro x hx
  have hx' : x ∈ HGraph.verts (V := V) s := HGraph.mem_verts_of_mem (V := V) he hx
  exact hfix x hx'

private lemma hgraph_rename_eq_self_of_le (f : V → V) {t s : HGraph V} (ht : t ≤ s)
    (hfix : ∀ x ∈ HGraph.verts (V := V) s, f x = x) : HGraph.rename f t = t := by
  apply hgraph_rename_eq_self_of_forall_mem (V := V) (f := f) (g := t)
  intro e he
  have he' : e ∈ s := Multiset.mem_of_le ht he
  have := hgraph_rename_eq_self_of_fix_verts (V := V) (f := f) (s := s) hfix
  -- use the vertex-fixing hypothesis directly on `e ∈ s`
  apply expr_rename_eq_self_of_forall_mem (V := V) (f := f) (e := e)
  intro x hx
  have hx' : x ∈ HGraph.verts (V := V) s := HGraph.mem_verts_of_mem (V := V) he' hx
  exact hfix x hx'

private lemma sigma_mem_verts_of_inLhs (e : sys.Event) {s : HGraph V} (happ : e.Applicable s)
    {p : P} (hp : ∃ ex ∈ (e.rule.lhs), p ∈ ex) : e.σ p ∈ HGraph.verts (V := V) s := by
  rcases hp with ⟨ex, hex, hp⟩
  have hexInput : Expr.rename e.σ ex ∈ e.input (sys := sys) := by
    -- `input = rename σ lhs`
    simpa [SystemFresh.Event.input, RuleFresh.instLhs, HGraph.rename] using
      (Multiset.mem_map_of_mem (Expr.rename e.σ) hex)
  have hexS : Expr.rename e.σ ex ∈ s := Multiset.mem_of_le happ hexInput
  have hσp : e.σ p ∈ Expr.rename e.σ ex := by
    simpa [Expr.rename] using (List.mem_map_of_mem (f := e.σ) hp)
  exact HGraph.mem_verts_of_mem (V := V) hexS hσp

private lemma sigma_fixed_of_inRhs (e : sys.Event) {s : HGraph V} (happ : e.Applicable s)
    (hwell : (e.rule).WellFormed) {p : P}
    (hpRhs : ∃ ex ∈ (e.rule.rhs), (Sum.inl p) ∈ ex)
    {n : Nat} {τ₁ τ₂ : Fin n → V} (hτ₁ : ∀ i, τ₁ i ∉ HGraph.verts (V := V) s)
    (hτ₂ : ∀ i, τ₂ i ∉ HGraph.verts (V := V) s) :
    swapPerm τ₁ τ₂ (e.σ p) = e.σ p := by
  have hpLhs : ∃ ex ∈ (e.rule.lhs), p ∈ ex := hwell p hpRhs
  have hmem : e.σ p ∈ HGraph.verts (V := V) s := sigma_mem_verts_of_inLhs (e := e) (s := s) happ hpLhs
  -- `e.σ p` lies in the "old" support, hence is fixed by the swap-permutation.
  simpa using swapPerm_fix_of_mem_verts (V := V) (τ₁ := τ₁) (τ₂ := τ₂) (s := s) hτ₁ hτ₂ hmem

lemma applyWith_rename_of_crossDisjoint (e : sys.Event) {s : HGraph V}
    (happ : e.Applicable s) (hwell : (e.rule).WellFormed)
    {τ₁ τ₂ : Fin (e.rule.nFresh) → V}
    (hτ₁ : e.FreshAssign τ₁ s) (hτ₂ : e.FreshAssign τ₂ s)
    (hdis : CrossDisjoint (V := V) τ₁ τ₂) :
    HGraph.rename (swapPerm τ₁ τ₂) (e.applyWith τ₁ s) = e.applyWith τ₂ s := by
  classical
  rcases hτ₁ with ⟨hinj₁, hfresh₁⟩
  rcases hτ₂ with ⟨hinj₂, hfresh₂⟩

  -- The swap-permutation fixes all vertices in the current state support.
  have hfixVerts : ∀ x ∈ HGraph.verts (V := V) s,
      swapPerm τ₁ τ₂ x = x := by
    intro x hx
    simpa using swapPerm_fix_of_mem_verts (V := V) (τ₁ := τ₁) (τ₂ := τ₂) (s := s) hfresh₁ hfresh₂ hx

  have hfix_s : HGraph.rename (swapPerm τ₁ τ₂) s = s :=
    hgraph_rename_eq_self_of_fix_verts (V := V) (f := swapPerm τ₁ τ₂) (s := s) hfixVerts

  have hfix_sub : HGraph.rename (swapPerm τ₁ τ₂) (s - e.input (sys := sys)) =
      (s - e.input (sys := sys)) := by
    apply hgraph_rename_eq_self_of_le (V := V)
      (f := swapPerm τ₁ τ₂)
      (t := s - e.input (sys := sys)) (s := s) (ht := Multiset.sub_le_self s (e.input (sys := sys))) hfixVerts

  have hfix_input : HGraph.rename (swapPerm τ₁ τ₂) (e.input (sys := sys)) =
      e.input (sys := sys) := by
    apply hgraph_rename_eq_self_of_le (V := V)
      (f := swapPerm τ₁ τ₂)
      (t := e.input (sys := sys)) (s := s) happ hfixVerts

  -- Rename the RHS instantiation: old vertices are fixed, fresh vertices are swapped componentwise.
  have hfix_sigma :
      ∀ p : P, (∃ ex ∈ (e.rule.rhs), (Sum.inl p) ∈ ex) →
        swapPerm τ₁ τ₂ (e.σ p) = e.σ p := by
    intro p hpRhs
    exact sigma_fixed_of_inRhs (e := e) (s := s) happ hwell (p := p) (τ₁ := τ₁) (τ₂ := τ₂) hpRhs hfresh₁ hfresh₂

  have hswap_tau : ∀ i, swapPerm τ₁ τ₂ (τ₁ i) = τ₂ i :=
    fun i => swapPerm_apply_left (V := V) (τ₁ := τ₁) (τ₂ := τ₂) hinj₁ hinj₂ hdis i

  have hRhs :
      HGraph.rename (swapPerm τ₁ τ₂) ((e.rule).instRhs e.σ τ₁) =
        (e.rule).instRhs e.σ τ₂ := by
    -- First, merge the two consecutive renamings on the RHS hypergraph using `rename_comp`.
    have hcomp :
        HGraph.rename (swapPerm τ₁ τ₂) ((e.rule).instRhs e.σ τ₁) =
          HGraph.rename (fun x =>
            swapPerm τ₁ τ₂ ((Sum.elim e.σ τ₁) x)) (e.rule).rhs := by
      simpa [RuleFresh.instRhs] using
        (HGraph.rename_comp (f := Sum.elim e.σ τ₁) (g := swapPerm τ₁ τ₂) (h := (e.rule).rhs)).symm

    -- Now show the two renaming functions agree on every vertex that actually appears in `rhs`.
    -- This avoids requiring global function extensionality on `Sum P (Fin n)`.
    have hrhs :
        HGraph.rename (fun x =>
            swapPerm τ₁ τ₂ ((Sum.elim e.σ τ₁) x)) (e.rule).rhs
          =
        HGraph.rename (Sum.elim e.σ τ₂) (e.rule).rhs := by
      -- `HGraph.rename` is a `Multiset.map` over expressions; use `map_congr` and `List.map_congr_left`.
      dsimp [HGraph.rename, Expr.rename]
      classical
      refine Multiset.map_congr rfl ?_
      intro ex hex
      -- show the two vertex-renaming maps agree on every vertex in this expression `ex`
      refine List.map_congr_left ?_
      intro x hx
      cases x with
      | inl p =>
          have hpRhs : ∃ ex' ∈ (e.rule).rhs, (Sum.inl p) ∈ ex' := ⟨ex, hex, hx⟩
          simpa [Sum.elim] using hfix_sigma p hpRhs
      | inr i =>
          simpa [Sum.elim] using hswap_tau i

    -- Finish.
    exact (hcomp.trans hrhs).trans (by simp [RuleFresh.instRhs])

  -- Put the pieces together.
  calc
    HGraph.rename (swapPerm τ₁ τ₂) (e.applyWith τ₁ s)
        = HGraph.rename (swapPerm τ₁ τ₂)
            ((s - e.input (sys := sys)) + (e.rule).instRhs e.σ τ₁) := by
              rfl
    _ = (HGraph.rename (swapPerm τ₁ τ₂) (s - e.input (sys := sys))) +
          (HGraph.rename (swapPerm τ₁ τ₂) ((e.rule).instRhs e.σ τ₁)) := by
          simp [HGraph.rename, Multiset.map_add]
    _ = (s - e.input (sys := sys)) + (e.rule).instRhs e.σ τ₂ := by
          rw [hfix_sub, hRhs]
    _ = e.applyWith τ₂ s := rfl

lemma applyWith_iso_of_crossDisjoint (e : sys.Event) {s : HGraph V}
    (happ : e.Applicable s) (hwell : (e.rule).WellFormed)
    {τ₁ τ₂ : Fin (e.rule.nFresh) → V}
    (hτ₁ : e.FreshAssign τ₁ s) (hτ₂ : e.FreshAssign τ₂ s)
    (hdis : CrossDisjoint (V := V) τ₁ τ₂) :
    HGraph.Iso (e.applyWith τ₁ s) (e.applyWith τ₂ s) := by
  refine ⟨swapPerm τ₁ τ₂, ?_⟩
  simpa using applyWith_rename_of_crossDisjoint (e := e) (s := s) happ hwell hτ₁ hτ₂ hdis

lemma applyWith_iso (e : sys.Event) [FreshSupply V] {s : HGraph V}
    (happ : e.Applicable s) (hwell : (e.rule).WellFormed)
    {τ₁ τ₂ : Fin (e.rule.nFresh) → V}
    (hτ₁ : e.FreshAssign τ₁ s) (hτ₂ : e.FreshAssign τ₂ s) :
    HGraph.Iso (e.applyWith τ₁ s) (e.applyWith τ₂ s) := by
  classical
  let forbidden : Finset V :=
    (HGraph.verts (V := V) s) ∪ (rangeFinset (V := V) τ₁) ∪ (rangeFinset (V := V) τ₂)
  let τ₃ : Fin (e.rule.nFresh) → V := FreshSupply.alloc (V := V) (e.rule.nFresh) forbidden
  have hτ₃ : e.FreshAssign τ₃ s := by
    have halloc := e.freshAssign_alloc (V := V) (s := s)
    -- `freshAssign_alloc` is for `alloc` with forbidden `verts s`; strengthen by shrinking.
    refine ⟨FreshSupply.alloc_injective (V := V) _ _, ?_⟩
    intro i
    have : τ₃ i ∉ forbidden := FreshSupply.alloc_not_mem (V := V) _ _ i
    intro hx
    exact this (by
      -- `verts s` is a subset of `forbidden`
      have : HGraph.verts (V := V) s ⊆ forbidden := by
        intro x hx
        simp [forbidden, hx]
      exact this hx)

  have hdis13 : CrossDisjoint (V := V) τ₁ τ₃ := by
    apply crossDisjoint_of_not_mem_range (V := V) (τ₁ := τ₁) (τ₂ := τ₃)
    intro j
    have hj : τ₃ j ∉ forbidden := FreshSupply.alloc_not_mem (V := V) _ _ j
    intro hmem
    exact hj (by
      -- `range τ₁ ⊆ forbidden`
      have : rangeFinset (V := V) τ₁ ⊆ forbidden := by
        intro x hx
        simp [forbidden, hx]
      exact this hmem)

  have hdis23 : CrossDisjoint (V := V) τ₂ τ₃ := by
    apply crossDisjoint_of_not_mem_range (V := V) (τ₁ := τ₂) (τ₂ := τ₃)
    intro j
    have hj : τ₃ j ∉ forbidden := FreshSupply.alloc_not_mem (V := V) _ _ j
    intro hmem
    exact hj (by
      have : rangeFinset (V := V) τ₂ ⊆ forbidden := by
        intro x hx
        simp [forbidden, hx]
      exact this hmem)

  have hiso13 : HGraph.Iso (e.applyWith τ₁ s) (e.applyWith τ₃ s) :=
    applyWith_iso_of_crossDisjoint (e := e) (s := s) happ hwell hτ₁ hτ₃ hdis13
  have hiso23 : HGraph.Iso (e.applyWith τ₂ s) (e.applyWith τ₃ s) :=
    applyWith_iso_of_crossDisjoint (e := e) (s := s) happ hwell hτ₂ hτ₃ hdis23
  -- `τ₂`-result is iso to `τ₃`-result, so `τ₃`-result is iso to `τ₂`-result.
  exact HGraph.Iso.trans hiso13 (HGraph.Iso.symm hiso23)

end Event

end SystemFresh

end Wolfram
end WPP
end HeytingLean
