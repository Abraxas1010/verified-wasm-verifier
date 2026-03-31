import Mathlib.Data.Multiset.AddSub
import HeytingLean.WPP.Wolfram.CausalInvarianceSingleLHS
import HeytingLean.WPP.Wolfram.WM148

namespace HeytingLean
namespace WPP
namespace Wolfram

/-!
# WM148 is causally invariant (branch-pair resolution, up to isomorphism)

We formalize the Wolfram Physics Project example from section *6.3 Causal Invariance*:

* rule: `{{x, y}} -> {{x, y}, {y, z}}` (one fresh vertex `z`)
* initial condition: `{{{0, 0}}}`

using the `SystemFresh` semantics with explicit fresh assignments. Causal invariance is
understood as **branch-pair resolution** up to vertex renaming (`HGraph.Iso`), as in
`CausalInvarianceSingleLHS.lean`.
-/

namespace WM148

open SystemFresh

/-!
## Small helpers

We need a simple fact about `HGraph.rename`: if a renaming fixes every vertex occurring in a
state, then it fixes the state.

This lemma is private in `RewriteFresh.lean`, so we re-prove a minimal version locally.
-/

private lemma expr_rename_eq_self_of_forall_mem {V : Type} (f : V → V) (e : Expr V)
    (h : ∀ x ∈ e, f x = x) : Expr.rename f e = e := by
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

private lemma hgraph_rename_eq_self_of_forall_mem {V : Type} (f : V → V) (g : HGraph V)
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
          simp [HGraph.rename]
        _ = a ::ₘ s := by
          rw [ha, htail]

private lemma hgraph_rename_eq_self_of_fix_verts {V : Type} [DecidableEq V] (f : V → V) (s : HGraph V)
    (hfix : ∀ x ∈ HGraph.verts (V := V) s, f x = x) : HGraph.rename f s = s := by
  apply hgraph_rename_eq_self_of_forall_mem (f := f) (g := s)
  intro e he
  apply expr_rename_eq_self_of_forall_mem (f := f) (e := e)
  intro x hx
  have hx' : x ∈ HGraph.verts (V := V) s := HGraph.mem_verts_of_mem (V := V) he hx
  exact hfix x hx'

private lemma multiset_foldl_singleton {α β : Type} (f : β → α → β) [RightCommutative f] (b : β) (a : α) :
    Multiset.foldl f b ({a} : Multiset α) = f b a := by
  rfl

private lemma verts_add_singleton {V : Type} [DecidableEq V] (g : HGraph V) (e : Expr V) :
    HGraph.verts (V := V) (g + ({e} : HGraph V)) = HGraph.verts (V := V) g ∪ e.toFinset := by
  classical
  -- `verts` is a commutative `foldl`, so `verts (g + {e})` is `verts g` union the vertices of `e`.
  simp [HGraph.verts, Multiset.foldl_add, multiset_foldl_singleton, HGraph.vertsStep]

/-!
## WM148: rewriting adds exactly one edge

For WM148, the RHS contains the LHS edge plus one new edge `[y, z]`, so applying any event
adds exactly one new edge.
-/

private lemma wm148_rule_eq (e : sys.Event) : e.rule = rule := by
  -- `sys.rules = [rule]`, and `e.idx : Fin 1`, so the only possible `get` is `rule`.
  have hlen : sys.rules.length = 1 := by
    simp [sys]
  have hlt : (e.idx : Nat) < 1 :=
    lt_of_lt_of_eq e.idx.isLt hlen
  have hidxNat : (e.idx : Nat) = 0 := Nat.lt_one_iff.mp hlt
  have h0 : (0 : Nat) < sys.rules.length := by
    rw [hlen]
    exact Nat.zero_lt_one
  have hidx : e.idx = ⟨0, h0⟩ := by
    apply Fin.ext
    exact hidxNat
  simp [SystemFresh.Event.rule, sys, hidx, rule]

private lemma wm148_nFresh (e : sys.Event) : e.rule.nFresh = 1 := by
  simpa [rule] using congrArg RuleFresh.nFresh (wm148_rule_eq (e := e))

private def fresh0 (e : sys.Event) : Fin e.rule.nFresh :=
  ⟨0, by
    have hn : e.rule.nFresh = 1 := wm148_nFresh (e := e)
    -- Avoid `simp`: it can rewrite `0 < 1` to `True`.
    rw [hn]
    exact Nat.zero_lt_one⟩

private lemma input_eq_singleton (e : sys.Event) :
    e.input (sys := sys) = ({[e.σ 0, e.σ 1]} : HGraph Nat) := by
  classical
  -- Keep `e.rule` intact (do not unfold it to `sys.rules.get ...`) so we can rewrite it.
  simp [-SystemFresh.Event.rule, SystemFresh.Event.input, RuleFresh.instLhs, wm148_rule_eq (e := e),
    rule, HGraph.rename, Expr.rename]

private lemma instRhs_eq_input_add_new (e : sys.Event) (τ : Fin e.rule.nFresh → Nat) :
    e.rule.instRhs e.σ τ =
      e.input (sys := sys) + ({[e.σ 1, τ (fresh0 (e := e))]} : HGraph Nat) := by
  classical
  -- We cannot use numerals for `Fin sys.rules.length`, so we case-split on the unique rule index.
  cases e with
  | mk idx σ =>
      -- `sys.rules.length = 1`, so `idx : Fin 1`; the only case is `idx = ⟨0, _⟩`.
      have hlen : sys.rules.length = 1 := by
        simp [sys]
      have hidxNat : (idx : Nat) = 0 := Nat.lt_one_iff.mp (lt_of_lt_of_eq idx.isLt hlen)
      -- Replace `idx` by the unique inhabitant `⟨0, _⟩`.
      have h0 : (0 : Nat) < sys.rules.length := by
        rw [hlen]
        exact Nat.zero_lt_one
      have hidx : idx = ⟨0, h0⟩ := by
        apply Fin.ext
        exact hidxNat
      -- Now everything computes directly from `rule.rhs`.
      subst hidx
      -- Compute `instRhs` and `input`.
      simp [SystemFresh.Event.rule, SystemFresh.Event.input, RuleFresh.instRhs, RuleFresh.instLhs,
        sys, rule, HGraph.rename, Expr.rename, fresh0]
      rfl

private lemma applyWith_eq_add_new (e : sys.Event) (τ : Fin e.rule.nFresh → Nat) (s : HGraph Nat)
    (happ : e.Applicable (sys := sys) s) :
    e.applyWith (sys := sys) τ s =
      s + ({[e.σ 1, τ (fresh0 (e := e))]} : HGraph Nat) := by
  classical
  have hcancel : s - e.input (sys := sys) + e.input (sys := sys) = s := Multiset.sub_add_cancel happ
  calc
    e.applyWith (sys := sys) τ s
        = (s - e.input (sys := sys)) + e.rule.instRhs e.σ τ := by
            rfl
    _ = (s - e.input (sys := sys)) +
          (e.input (sys := sys) + ({[e.σ 1, τ (fresh0 (e := e))]} : HGraph Nat)) := by
          rw [instRhs_eq_input_add_new (e := e) (τ := τ)]
    _ = (s - e.input (sys := sys) + e.input (sys := sys)) +
          ({[e.σ 1, τ (fresh0 (e := e))]} : HGraph Nat) := by
          ac_rfl
    _ = s + ({[e.σ 1, τ (fresh0 (e := e))]} : HGraph Nat) := by
          rw [hcancel]

/-!
## Causal invariance for WM148

The key fact is that WM148 rewrites are *monotone*: they never remove edges, they only add a
new edge `[y, z]`. Therefore:

* if two branches rewrite the same input edge, they are immediately isomorphic (swap the two fresh names);
* if they rewrite distinct input edges, apply the other update once on each branch to resolve the fork
  (again up to swapping fresh names when needed).
-/

theorem causalInvariant : SystemFresh.CausalInvariant (sys := sys) := by
  classical
  intro a b c hab hac
  rcases hab with ⟨e1, τ1, happ1, hfresh1, rfl⟩
  rcases hac with ⟨e2, τ2, happ2, hfresh2, rfl⟩

  -- First-step fresh vertices (there is exactly one in WM148).
  let z1 : Nat := τ1 (fresh0 (e := e1))
  let z2 : Nat := τ2 (fresh0 (e := e2))
  have hz1_not : z1 ∉ HGraph.verts (V := Nat) a := by
    simpa [z1] using (hfresh1.2 (fresh0 (e := e1)))
  have hz2_not : z2 ∉ HGraph.verts (V := Nat) a := by
    simpa [z2] using (hfresh2.2 (fresh0 (e := e2)))

  -- Expand the first-step results as "add one edge".
  have hb1 : e1.applyWith (sys := sys) τ1 a = a + ({[e1.σ 1, z1]} : HGraph Nat) := by
    simpa [z1] using applyWith_eq_add_new (e := e1) (τ := τ1) (s := a) happ1
  have hc1 : e2.applyWith (sys := sys) τ2 a = a + ({[e2.σ 1, z2]} : HGraph Nat) := by
    simpa [z2] using applyWith_eq_add_new (e := e2) (τ := τ2) (s := a) happ2

  -- Case split: do the two branches rewrite the same input edge?
  by_cases hin : e1.input (sys := sys) = e2.input (sys := sys)
  · -- Same input: 0 extra steps; the results are isomorphic by swapping the fresh vertices.
    -- Extract `y := σ 1` equality from the singleton input hypergraphs.
    have hedgeEq :
        ([e1.σ 0, e1.σ 1] : Expr Nat) = ([e2.σ 0, e2.σ 1] : Expr Nat) := by
      have h1 : ([e1.σ 0, e1.σ 1] : Expr Nat) ∈ e1.input (sys := sys) := by
        rw [input_eq_singleton (e := e1)]
        simp
      have h2 : ([e1.σ 0, e1.σ 1] : Expr Nat) ∈ e2.input (sys := sys) := by
        rw [hin.symm]
        exact h1
      -- membership in a singleton multiset is equality
      have h2' := h2
      rw [input_eq_singleton (e := e2)] at h2'
      simpa using h2'

    have hy : e1.σ 1 = e2.σ 1 := by
      -- Extract the second component from a 2-element list equality.
      have hcons :
          (e1.σ 0 :: [e1.σ 1] : List Nat) = (e2.σ 0 :: [e2.σ 1] : List Nat) := by
        simpa using hedgeEq
      have htail : ([e1.σ 1] : List Nat) = [e2.σ 1] :=
        (List.cons.inj hcons).2
      have hsingle : (e1.σ 1 :: ([] : List Nat)) = (e2.σ 1 :: ([] : List Nat)) := by
        simpa using htail
      exact (List.cons.inj hsingle).1

    -- The endpoint `y = σ 1` lies in `verts a` because the input edge is present.
    have hy_mem : e1.σ 1 ∈ HGraph.verts (V := Nat) a := by
      have hEdgeInInput : ([e1.σ 0, e1.σ 1] : Expr Nat) ∈ e1.input (sys := sys) := by
        rw [input_eq_singleton (e := e1)]
        simp
      have hEdgeInA : ([e1.σ 0, e1.σ 1] : Expr Nat) ∈ a := Multiset.mem_of_le happ1 hEdgeInInput
      exact HGraph.mem_verts_of_mem (V := Nat) (e := ([e1.σ 0, e1.σ 1] : Expr Nat)) (g := a) hEdgeInA
        (by simp)

    let p : Equiv.Perm Nat := Equiv.swap z1 z2
    have hp_fix_a : HGraph.rename p a = a := by
      apply hgraph_rename_eq_self_of_fix_verts (V := Nat) (f := p) (s := a)
      intro x hx
      have hx1 : x ≠ z1 := by intro h; exact hz1_not (h ▸ hx)
      have hx2 : x ≠ z2 := by intro h; exact hz2_not (h ▸ hx)
      simpa [p] using (Equiv.swap_apply_of_ne_of_ne hx1 hx2)

    have hp_y : p (e1.σ 1) = e1.σ 1 := by
      have hy_ne_z1 : e1.σ 1 ≠ z1 := by intro h; exact hz1_not (h ▸ hy_mem)
      have hy_ne_z2 : e1.σ 1 ≠ z2 := by intro h; exact hz2_not (h ▸ hy_mem)
      simpa [p] using (Equiv.swap_apply_of_ne_of_ne hy_ne_z1 hy_ne_z2)

    have hp_on_b :
        HGraph.rename p (e1.applyWith (sys := sys) τ1 a) = e2.applyWith (sys := sys) τ2 a := by
      -- rewrite both sides as `a + {[y, z]}` and compute `rename` explicitly
      have hp_z1 : p z1 = z2 := by simp [p]
      calc
        HGraph.rename p (e1.applyWith (sys := sys) τ1 a)
            = HGraph.rename p (a + ({[e1.σ 1, z1]} : HGraph Nat)) := by
                simp [hb1]
        _ = HGraph.rename p a + HGraph.rename p ({[e1.σ 1, z1]} : HGraph Nat) := by
              simp [HGraph.rename, Multiset.map_add]
        _ = a + ({[e2.σ 1, z2]} : HGraph Nat) := by
              -- first `rename p a = a`
              rw [hp_fix_a]
              -- then compute the singleton-edge renaming, and rewrite `p` on the relevant vertices
              simp [HGraph.rename, Expr.rename, Multiset.map_singleton]
              rw [hp_y, hp_z1, hy]
              simp
        _ = e2.applyWith (sys := sys) τ2 a := by
              simp [hc1]

    refine ⟨_, _, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl, ⟨p, hp_on_b⟩⟩
  · -- Distinct inputs: apply the *other* update once on each branch to resolve.
    let b1 : HGraph Nat := e1.applyWith (sys := sys) τ1 a
    let c1 : HGraph Nat := e2.applyWith (sys := sys) τ2 a

    have hb1_def : b1 = a + ({[e1.σ 1, z1]} : HGraph Nat) := by
      simp [b1, hb1]
    have hc1_def : c1 = a + ({[e2.σ 1, z2]} : HGraph Nat) := by
      simp [c1, hc1]

    -- Applicability of the other event is preserved because WM148 only adds edges.
    have hb1_app : e2.Applicable (sys := sys) b1 := by
      have : a ≤ b1 := by
        rw [hb1_def]
        exact Multiset.le_add_right a ({[e1.σ 1, z1]} : HGraph Nat)
      exact le_trans happ2 this

    have hc1_app : e1.Applicable (sys := sys) c1 := by
      have : a ≤ c1 := by
        rw [hc1_def]
        exact Multiset.le_add_right a ({[e2.σ 1, z2]} : HGraph Nat)
      exact le_trans happ1 this

    -- Two ways to resolve, depending on whether the first-step fresh names coincide.
    by_cases hzz : z1 = z2
    · -- If the fresh names coincide, use a new fresh name `w` for both second steps and swap `z ↔ w`.
      let forbidden : Finset Nat := (HGraph.verts (V := Nat) a) ∪ {z1}
      let w : Nat := freshNat forbidden
      have hw_not_forbidden : w ∉ forbidden := freshNat_not_mem forbidden
      have hw_not_a : w ∉ HGraph.verts (V := Nat) a := by
        intro hw
        exact hw_not_forbidden (by simp [forbidden, hw])
      have hw_ne_z : w ≠ z1 := by
        intro hEq
        exact hw_not_forbidden (by simp [forbidden, hEq])

      -- Fresh assignments for the second steps (constant, since `nFresh = 1`).
      let τ2' : Fin e2.rule.nFresh → Nat := fun _ => w
      let τ1' : Fin e1.rule.nFresh → Nat := fun _ => w

      have hτ2' : e2.FreshAssign (sys := sys) τ2' b1 := by
        have hn : e2.rule.nFresh = 1 := wm148_nFresh (e := e2)
        haveI : Subsingleton (Fin e2.rule.nFresh) := by
          simpa [hn] using (inferInstance : Subsingleton (Fin 1))
        refine ⟨?_, ?_⟩
        · intro i j _h
          exact Subsingleton.elim i j
        · intro i
          have hw_not_b1 : w ∉ HGraph.verts (V := Nat) b1 := by
            -- `verts b1 = verts a ∪ {y1, z1}`, and `w` is not in `verts a` or `{z1}`.
            have hv : HGraph.verts (V := Nat) b1 = HGraph.verts (V := Nat) a ∪ ([e1.σ 1, z1] : Expr Nat).toFinset := by
              simpa [hb1_def] using verts_add_singleton (V := Nat) a ([e1.σ 1, z1] : Expr Nat)
            intro hw
            have hw' : w ∈ HGraph.verts (V := Nat) a ∪ ([e1.σ 1, z1] : Expr Nat).toFinset := by
              simpa [hv] using hw
            have : w ∈ HGraph.verts (V := Nat) a ∨ w ∈ ([e1.σ 1, z1] : Expr Nat).toFinset :=
              Finset.mem_union.mp hw'
            rcases this with hwA | hwEdge
            · exact hw_not_a hwA
            · have : w = e1.σ 1 ∨ w = z1 := by
                have hwEdgeList : w ∈ ([e1.σ 1, z1] : Expr Nat) := by
                  simpa [List.mem_toFinset] using hwEdge
                simpa using hwEdgeList
              rcases this with hwy | hwz
              · have : e1.σ 1 ∈ HGraph.verts (V := Nat) a := by
                  -- input edge is present, so `σ 1` is a vertex of `a`
                  have hEdgeInInput :
                      ([e1.σ 0, e1.σ 1] : Expr Nat) ∈ e1.input (sys := sys) := by
                    rw [input_eq_singleton (e := e1)]
                    simp
                  have hEdgeInA :
                      ([e1.σ 0, e1.σ 1] : Expr Nat) ∈ a :=
                    Multiset.mem_of_le happ1 hEdgeInInput
                  exact
                    HGraph.mem_verts_of_mem (V := Nat) (e := ([e1.σ 0, e1.σ 1] : Expr Nat)) (g := a) hEdgeInA
                      (by simp)
                exact hw_not_a (hwy ▸ this)
              · exact hw_ne_z hwz
          simpa [τ2'] using hw_not_b1

      have hτ1' : e1.FreshAssign (sys := sys) τ1' c1 := by
        have hn : e1.rule.nFresh = 1 := wm148_nFresh (e := e1)
        haveI : Subsingleton (Fin e1.rule.nFresh) := by
          simpa [hn] using (inferInstance : Subsingleton (Fin 1))
        refine ⟨?_, ?_⟩
        · intro i j _h
          exact Subsingleton.elim i j
        · intro i
          have hw_not_c1 : w ∉ HGraph.verts (V := Nat) c1 := by
            have hv : HGraph.verts (V := Nat) c1 = HGraph.verts (V := Nat) a ∪ ([e2.σ 1, z2] : Expr Nat).toFinset := by
              simpa [hc1_def] using verts_add_singleton (V := Nat) a ([e2.σ 1, z2] : Expr Nat)
            intro hw
            have hw' : w ∈ HGraph.verts (V := Nat) a ∪ ([e2.σ 1, z2] : Expr Nat).toFinset := by
              simpa [hv] using hw
            have : w ∈ HGraph.verts (V := Nat) a ∨ w ∈ ([e2.σ 1, z2] : Expr Nat).toFinset :=
              Finset.mem_union.mp hw'
            rcases this with hwA | hwEdge
            · exact hw_not_a hwA
            · have : w = e2.σ 1 ∨ w = z2 := by
                have hwEdgeList : w ∈ ([e2.σ 1, z2] : Expr Nat) := by
                  simpa [List.mem_toFinset] using hwEdge
                simpa using hwEdgeList
              rcases this with hwy | hwz
              · have : e2.σ 1 ∈ HGraph.verts (V := Nat) a := by
                  have hEdgeInInput :
                      ([e2.σ 0, e2.σ 1] : Expr Nat) ∈ e2.input (sys := sys) := by
                    rw [input_eq_singleton (e := e2)]
                    simp
                  have hEdgeInA :
                      ([e2.σ 0, e2.σ 1] : Expr Nat) ∈ a :=
                    Multiset.mem_of_le happ2 hEdgeInInput
                  exact
                    HGraph.mem_verts_of_mem (V := Nat) (e := ([e2.σ 0, e2.σ 1] : Expr Nat)) (g := a) hEdgeInA
                      (by simp)
                exact hw_not_a (hwy ▸ this)
              · -- `z2 = z1` in this branch
                have : z2 = z1 := hzz.symm
                exact hw_ne_z (this ▸ hwz)
          simpa [τ1'] using hw_not_c1

      let b2 : HGraph Nat := e2.applyWith (sys := sys) τ2' b1
      let c2 : HGraph Nat := e1.applyWith (sys := sys) τ1' c1

      have hb_step : SystemFresh.StepWith (sys := sys) b1 b2 := by
        refine ⟨e2, τ2', hb1_app, hτ2', rfl⟩
      have hc_step : SystemFresh.StepWith (sys := sys) c1 c2 := by
        refine ⟨e1, τ1', hc1_app, hτ1', rfl⟩

      have hb2_def : b2 = a + ({[e1.σ 1, z1]} : HGraph Nat) + ({[e2.σ 1, w]} : HGraph Nat) := by
        -- `b2 = b1 + {[e2.σ 1, w]}`
        have : b2 = b1 + ({[e2.σ 1, w]} : HGraph Nat) := by
          simpa [b2, τ2'] using applyWith_eq_add_new (e := e2) (τ := τ2') (s := b1) hb1_app
        simp [this, hb1_def, add_assoc]

      have hc2_def : c2 = a + ({[e2.σ 1, z2]} : HGraph Nat) + ({[e1.σ 1, w]} : HGraph Nat) := by
        have : c2 = c1 + ({[e1.σ 1, w]} : HGraph Nat) := by
          simpa [c2, τ1'] using applyWith_eq_add_new (e := e1) (τ := τ1') (s := c1) hc1_app
        simp [this, hc1_def, add_assoc]

      -- Show `rename (swap z w)` maps `b2` to `c2` (using `z2 = z1`).
      let p : Equiv.Perm Nat := Equiv.swap z1 w
      have hp_fix_a : HGraph.rename p a = a := by
        apply hgraph_rename_eq_self_of_fix_verts (V := Nat) (f := p) (s := a)
        intro x hx
        have hxz : x ≠ z1 := by intro h; exact hz1_not (h ▸ hx)
        have hxw : x ≠ w := by intro h; exact hw_not_a (h ▸ hx)
        simpa [p] using (Equiv.swap_apply_of_ne_of_ne hxz hxw)

      have hp_y1 : p (e1.σ 1) = e1.σ 1 := by
        have hy1_mem : e1.σ 1 ∈ HGraph.verts (V := Nat) a := by
          have hEdgeInInput : ([e1.σ 0, e1.σ 1] : Expr Nat) ∈ e1.input (sys := sys) := by
            rw [input_eq_singleton (e := e1)]
            simp
          have hEdgeInA : ([e1.σ 0, e1.σ 1] : Expr Nat) ∈ a := Multiset.mem_of_le happ1 hEdgeInInput
          exact HGraph.mem_verts_of_mem (V := Nat) (e := ([e1.σ 0, e1.σ 1] : Expr Nat)) (g := a) hEdgeInA (by simp)
        have hy1_ne_z : e1.σ 1 ≠ z1 := by intro h; exact hz1_not (h ▸ hy1_mem)
        have hy1_ne_w : e1.σ 1 ≠ w := by intro h; exact hw_not_a (h ▸ hy1_mem)
        simpa [p] using (Equiv.swap_apply_of_ne_of_ne hy1_ne_z hy1_ne_w)

      have hp_y2 : p (e2.σ 1) = e2.σ 1 := by
        have hy2_mem : e2.σ 1 ∈ HGraph.verts (V := Nat) a := by
          have hEdgeInInput : ([e2.σ 0, e2.σ 1] : Expr Nat) ∈ e2.input (sys := sys) := by
            rw [input_eq_singleton (e := e2)]
            simp
          have hEdgeInA : ([e2.σ 0, e2.σ 1] : Expr Nat) ∈ a := Multiset.mem_of_le happ2 hEdgeInInput
          exact HGraph.mem_verts_of_mem (V := Nat) (e := ([e2.σ 0, e2.σ 1] : Expr Nat)) (g := a) hEdgeInA (by simp)
        have hy2_ne_z : e2.σ 1 ≠ z1 := by
          intro h
          exact hz1_not (h ▸ hy2_mem)
        have hy2_ne_w : e2.σ 1 ≠ w := by
          intro h
          exact hw_not_a (h ▸ hy2_mem)
        simpa [p] using (Equiv.swap_apply_of_ne_of_ne hy2_ne_z hy2_ne_w)

      have hp_on_b2 : HGraph.rename p b2 = c2 := by
        -- Use the explicit normal forms and compute renaming.
        have hp_z : p z1 = w := by simp [p]
        have hp_w : p w = z1 := by simp [p]
        calc
          HGraph.rename p b2
              = HGraph.rename p (a + ({[e1.σ 1, z1]} : HGraph Nat) + ({[e2.σ 1, w]} : HGraph Nat)) := by
                  simp [hb2_def]
          _ = HGraph.rename p a +
                HGraph.rename p ({[e1.σ 1, z1]} : HGraph Nat) +
                HGraph.rename p ({[e2.σ 1, w]} : HGraph Nat) := by
                  simp [HGraph.rename, Multiset.map_add, add_assoc]
          _ = a +
                HGraph.rename p ({[e1.σ 1, z1]} : HGraph Nat) +
                HGraph.rename p ({[e2.σ 1, w]} : HGraph Nat) := by
                  rw [hp_fix_a]
          _ = a + ({[e1.σ 1, w]} : HGraph Nat) + ({[e2.σ 1, z1]} : HGraph Nat) := by
                  simp [HGraph.rename, Expr.rename, Multiset.map_singleton]
                  rw [hp_y1, hp_z, hp_y2, hp_w]
          _ = c2 := by
                  -- Use `z2 = z1` and the explicit form of `c2`.
                  simp [hc2_def, hzz, add_assoc, add_left_comm, add_comm]

      refine ⟨b2, c2,
        Relation.ReflTransGen.single hb_step,
        Relation.ReflTransGen.single hc_step,
        ⟨p, hp_on_b2⟩⟩
    · -- If the first-step fresh names are distinct, reuse them crosswise to make the join state literally equal.
      have hz2_not_b1 : z2 ∉ HGraph.verts (V := Nat) b1 := by
        have hv : HGraph.verts (V := Nat) b1 = HGraph.verts (V := Nat) a ∪ ([e1.σ 1, z1] : Expr Nat).toFinset := by
          simpa [hb1_def] using verts_add_singleton (V := Nat) a ([e1.σ 1, z1] : Expr Nat)
        intro hz2
        have hz2' : z2 ∈ HGraph.verts (V := Nat) a ∪ ([e1.σ 1, z1] : Expr Nat).toFinset := by
          simpa [hv] using hz2
        have : z2 ∈ HGraph.verts (V := Nat) a ∨ z2 ∈ ([e1.σ 1, z1] : Expr Nat).toFinset :=
          Finset.mem_union.mp hz2'
        rcases this with hz2A | hz2Edge
        · exact hz2_not hz2A
        · have : z2 = e1.σ 1 ∨ z2 = z1 := by
            have hz2EdgeList : z2 ∈ ([e1.σ 1, z1] : Expr Nat) := by
              simpa [List.mem_toFinset] using hz2Edge
            simpa using hz2EdgeList
          rcases this with hz2y | hz2z1
          · -- `e1.σ 1 ∈ verts a`, so `z2 = e1.σ 1` contradicts `z2 ∉ verts a`.
            have hy1_mem : e1.σ 1 ∈ HGraph.verts (V := Nat) a := by
              have hEdgeInInput :
                  ([e1.σ 0, e1.σ 1] : Expr Nat) ∈ e1.input (sys := sys) := by
                rw [input_eq_singleton (e := e1)]
                simp
              have hEdgeInA :
                  ([e1.σ 0, e1.σ 1] : Expr Nat) ∈ a :=
                Multiset.mem_of_le happ1 hEdgeInInput
              exact
                HGraph.mem_verts_of_mem (V := Nat) (e := ([e1.σ 0, e1.σ 1] : Expr Nat)) (g := a) hEdgeInA
                  (by simp)
            exact hz2_not (hz2y ▸ hy1_mem)
          · exact hzz (hz2z1 ▸ rfl)

      have hz1_not_c1 : z1 ∉ HGraph.verts (V := Nat) c1 := by
        have hv : HGraph.verts (V := Nat) c1 = HGraph.verts (V := Nat) a ∪ ([e2.σ 1, z2] : Expr Nat).toFinset := by
          simpa [hc1_def] using verts_add_singleton (V := Nat) a ([e2.σ 1, z2] : Expr Nat)
        intro hz1
        have hz1' : z1 ∈ HGraph.verts (V := Nat) a ∪ ([e2.σ 1, z2] : Expr Nat).toFinset := by
          simpa [hv] using hz1
        have : z1 ∈ HGraph.verts (V := Nat) a ∨ z1 ∈ ([e2.σ 1, z2] : Expr Nat).toFinset :=
          Finset.mem_union.mp hz1'
        rcases this with hz1A | hz1Edge
        · exact hz1_not hz1A
        · have : z1 = e2.σ 1 ∨ z1 = z2 := by
            have hz1EdgeList : z1 ∈ ([e2.σ 1, z2] : Expr Nat) := by
              simpa [List.mem_toFinset] using hz1Edge
            simpa using hz1EdgeList
          rcases this with hz1y | hz1z2
          · have hy2_mem : e2.σ 1 ∈ HGraph.verts (V := Nat) a := by
              have hEdgeInInput :
                  ([e2.σ 0, e2.σ 1] : Expr Nat) ∈ e2.input (sys := sys) := by
                rw [input_eq_singleton (e := e2)]
                simp
              have hEdgeInA :
                  ([e2.σ 0, e2.σ 1] : Expr Nat) ∈ a :=
                Multiset.mem_of_le happ2 hEdgeInInput
              exact
                HGraph.mem_verts_of_mem (V := Nat) (e := ([e2.σ 0, e2.σ 1] : Expr Nat)) (g := a) hEdgeInA
                  (by simp)
            exact hz1_not (hz1y ▸ hy2_mem)
          · exact hzz (hz1z2 ▸ rfl)

      let τ2' : Fin e2.rule.nFresh → Nat := fun _ => z2
      let τ1' : Fin e1.rule.nFresh → Nat := fun _ => z1

      have hτ2' : e2.FreshAssign (sys := sys) τ2' b1 := by
        have hn : e2.rule.nFresh = 1 := wm148_nFresh (e := e2)
        haveI : Subsingleton (Fin e2.rule.nFresh) := by
          simpa [hn] using (inferInstance : Subsingleton (Fin 1))
        refine ⟨?_, ?_⟩
        · intro i j _h
          exact Subsingleton.elim i j
        · intro i
          simpa [τ2'] using hz2_not_b1

      have hτ1' : e1.FreshAssign (sys := sys) τ1' c1 := by
        have hn : e1.rule.nFresh = 1 := wm148_nFresh (e := e1)
        haveI : Subsingleton (Fin e1.rule.nFresh) := by
          simpa [hn] using (inferInstance : Subsingleton (Fin 1))
        refine ⟨?_, ?_⟩
        · intro i j _h
          exact Subsingleton.elim i j
        · intro i
          simpa [τ1'] using hz1_not_c1

      let b2 : HGraph Nat := e2.applyWith (sys := sys) τ2' b1
      let c2 : HGraph Nat := e1.applyWith (sys := sys) τ1' c1

      have hb_step : SystemFresh.StepWith (sys := sys) b1 b2 := by
        refine ⟨e2, τ2', hb1_app, hτ2', rfl⟩
      have hc_step : SystemFresh.StepWith (sys := sys) c1 c2 := by
        refine ⟨e1, τ1', hc1_app, hτ1', rfl⟩

      have hb2_def : b2 = a + ({[e1.σ 1, z1]} : HGraph Nat) + ({[e2.σ 1, z2]} : HGraph Nat) := by
        have : b2 = b1 + ({[e2.σ 1, z2]} : HGraph Nat) := by
          simpa [b2, τ2', z2] using applyWith_eq_add_new (e := e2) (τ := τ2') (s := b1) hb1_app
        simp [this, hb1_def, add_assoc]

      have hc2_def : c2 = a + ({[e2.σ 1, z2]} : HGraph Nat) + ({[e1.σ 1, z1]} : HGraph Nat) := by
        have : c2 = c1 + ({[e1.σ 1, z1]} : HGraph Nat) := by
          simpa [c2, τ1', z1] using applyWith_eq_add_new (e := e1) (τ := τ1') (s := c1) hc1_app
        simp [this, hc1_def, add_assoc]

      have heq : b2 = c2 := by
        -- by commutativity/associativity of `Multiset` addition
        simp [hb2_def, hc2_def, add_assoc, add_left_comm, add_comm]

      refine ⟨b2, c2,
        Relation.ReflTransGen.single hb_step,
        Relation.ReflTransGen.single hc_step,
        (heq ▸ HGraph.Iso.refl b2)⟩

end WM148

end Wolfram
end WPP
end HeytingLean
