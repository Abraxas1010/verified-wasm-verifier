import HeytingLean.Genesis.CantorWitness
import HeytingLean.Genesis.LatticeNucleusBridge
import HeytingLean.LoF.LoFSecond.Syntax
import Mathlib.Order.Nucleus

open scoped Classical

/-!
# Genesis.Stabilization

Phase-3 stabilization layer:
- depth-truncated `unroll : Nat → CoGame → PGame`
- `unroll 0 Life = PGame.zero`
- interpretation anchors (Void/Life/unroll-Life)
- nucleus-style algebraic correspondences on interpreted supports
-/

namespace HeytingLean.Genesis

open CoGame

/-- Re-root a co-game at a chosen node. -/
noncomputable def reroot (G : CoGame) (r : G.Node) : CoGame where
  Node := G.Node
  root := r
  leftSucc := G.leftSucc
  rightSucc := G.rightSucc

/-- Depth-truncated unrolling from coinductive graph games into well-founded `PGame`s. -/
noncomputable def unroll : Nat → CoGame → SetTheory.PGame
  | 0, _ => 0
  | Nat.succ n, G =>
      SetTheory.PGame.mk
        (ULift ({x : G.Node // x ∈ G.leftSucc G.root}))
        (ULift ({x : G.Node // x ∈ G.rightSucc G.root}))
        (fun i => unroll n (reroot G i.down.1))
        (fun j => unroll n (reroot G j.down.1))

@[simp] theorem unroll_zero (G : CoGame) : unroll 0 G = (0 : SetTheory.PGame) := rfl
@[simp] theorem unroll_zero_life : unroll 0 CoGame.Life = (0 : SetTheory.PGame) := rfl

/-- LoF expression vocabulary used for approximation-level interpretation. -/
abbrev LoFExpr0 := HeytingLean.LoF.LoFSecond.Expr 0

/-- Finite nesting used for stabilized approximants. -/
def nesting : Nat → LoFExpr0
  | 0 => .void
  | Nat.succ n => .mark (nesting n)

/-- Oscillation-level interpretation (pre-stabilization signal). -/
noncomputable def oscillationExpr (G : CoGame) : LoFExpr0 :=
  if G.root ∈ G.leftSucc G.root ∧ G.root ∈ G.rightSucc G.root then
    .reentry
  else
    .void

@[simp] theorem oscillationExpr_void : oscillationExpr CoGame.Void = .void := by
  simp [oscillationExpr, CoGame.Void]

@[simp] theorem oscillationExpr_life : oscillationExpr CoGame.Life = .reentry := by
  simp [oscillationExpr, CoGame.Life]

/-- Interpretation of truncated games at depth `n`. -/
def interpretUnroll : Nat → SetTheory.PGame → LoFExpr0
  | 0, _ => .void
  | Nat.succ n, _ => .mark (interpretUnroll n (0 : SetTheory.PGame))

theorem interpretUnroll_eq_nesting (n : Nat) (g : SetTheory.PGame) :
    interpretUnroll n g = nesting n := by
  induction n generalizing g with
  | zero =>
      rfl
  | succ n ih =>
      simp [interpretUnroll, nesting, ih (0 : SetTheory.PGame)]

/-- Layer-1 anchor: finite unrolling of Life maps to finite nesting. -/
theorem interpret_unroll_life_anchor (n : Nat) :
    interpretUnroll n (unroll n CoGame.Life) = nesting n := by
  simpa using interpretUnroll_eq_nesting n (unroll n CoGame.Life)

/-- Support carrier used for nucleus-style correspondence lemmas. -/
abbrev Support := Set Nat

/-- A simple closure nucleus adding the base boundary witness `0`. -/
def collapseNucleus : Nucleus Support where
  toInfHom :=
    { toFun := fun S => S ∪ ({0} : Set Nat)
      map_inf' := by
        intro A B
        ext x
        constructor
        · intro hx
          rcases hx with hx | hx
          · exact ⟨Or.inl hx.1, Or.inl hx.2⟩
          · exact ⟨Or.inr hx, Or.inr hx⟩
        · intro hx
          rcases hx with ⟨hxA, hxB⟩
          rcases hxA with hxA | hxA
          · rcases hxB with hxB | hxB
            · exact Or.inl ⟨hxA, hxB⟩
            · exact Or.inr hxB
          · exact Or.inr hxA }
  idempotent' := by
    intro S
    intro x hx
    simp at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr hx
  le_apply' := by
    intro S
    intro x hx
    exact Or.inl hx

@[simp] theorem collapseNucleus_apply (S : Support) :
    collapseNucleus S = S ∪ ({0} : Set Nat) := rfl

/-- Support semantics for second-degree LoF expressions. -/
def exprSupport : LoFExpr0 → Support
  | .void => ∅
  | .var _ => ∅
  | .reentry => ({0} : Set Nat)
  | .mark e => Nat.succ '' exprSupport e
  | .juxt a b => exprSupport a ∪ exprSupport b

/-- Layer-2 (extensive): interpreted support lies below its closure. -/
theorem collapse_extensive (S : Support) : S ⊆ collapseNucleus S :=
  Nucleus.le_apply (n := collapseNucleus) (x := S)

/-- Layer-2 (idempotence): closure at stabilized depth is fixed. -/
theorem collapse_idempotent (S : Support) :
    collapseNucleus (collapseNucleus S) = collapseNucleus S :=
  Nucleus.idempotent (n := collapseNucleus) (x := S)

/-- Layer-2 (meet compatibility): closure preserves intersections. -/
theorem collapse_inf (A B : Support) :
    collapseNucleus (A ⊓ B) = collapseNucleus A ⊓ collapseNucleus B :=
  Nucleus.map_inf (n := collapseNucleus) (x := A) (y := B)

/-- Layer-2 packaged on Life approximants. -/
def lifeApproxExpr (n : Nat) : LoFExpr0 :=
  interpretUnroll n (unroll n CoGame.Life : SetTheory.PGame.{0})

theorem unroll_nucleus_layer2 (n : Nat) :
    collapseNucleus (exprSupport (lifeApproxExpr n))
      =
      collapseNucleus (collapseNucleus (exprSupport (lifeApproxExpr n))) :=
  (collapse_idempotent (exprSupport (lifeApproxExpr n))).symm

/-! ## Tier-1 claim-surface theorem (LEP T1.2 alias in stabilization path) -/

/-- Stabilization-path alias to the lattice/LoF fixed-point bridge equivalence. -/
def stabilization_lattice_lof_isomorphism :
    EmergentFixed ≃ LoFFixed :=
  lattice_lof_isomorphism

/-! ## Phase-6: dual stabilization criteria (signature + nucleus) -/

/-- Signature view of witness dynamics.
`0` reads the oscillation boundary, positive depths repeatedly mark if the boundary is re-entry. -/
noncomputable def sigProfile : Nat → CoGame → LoFExpr0
  | 0, G => oscillationExpr G
  | Nat.succ n, G =>
      if oscillationExpr G = (.void : LoFExpr0) then
        .void
      else
        .mark (sigProfile n G)

/-- Signature stabilization at depth `n`: two consecutive profiles coincide. -/
def stabilizesAt_sig (n : Nat) (G : CoGame) : Prop :=
  sigProfile (Nat.succ n) G = sigProfile n G

/-- Signature eventual stabilization: stabilization occurs at some depth. -/
def eventualStabilizes_sig (G : CoGame) : Prop :=
  ∃ n : Nat, stabilizesAt_sig n G

/-- Nucleus-side support profile induced by signature dynamics. -/
noncomputable def supportProfile (n : Nat) (G : CoGame) : Support :=
  exprSupport (sigProfile n G)

/-- Nucleus stabilization at depth `n`: closure of consecutive supports agrees. -/
def stabilizesAt_nucleus (n : Nat) (G : CoGame) : Prop :=
  collapseNucleus (supportProfile (Nat.succ n) G) = collapseNucleus (supportProfile n G)

/-- Nucleus eventual stabilization: closure stabilization occurs at some depth. -/
def eventualStabilizes_nucleus (G : CoGame) : Prop :=
  ∃ n : Nat, stabilizesAt_nucleus n G

/-- Combined Phase-6 criterion: both views hold. -/
def eventualStabilizes (G : CoGame) : Prop :=
  eventualStabilizes_sig G ∧ eventualStabilizes_nucleus G

theorem oscillationExpr_cases (G : CoGame) :
    oscillationExpr G = (.void : LoFExpr0) ∨ oscillationExpr G = .reentry := by
  unfold oscillationExpr
  by_cases h :
      G.root ∈ G.leftSucc G.root ∧
        G.root ∈ G.rightSucc G.root
  · right
    simp [h]
  · left
    simp [h]

theorem stabilizesAt_sig_zero_of_void {G : CoGame} (h : oscillationExpr G = (.void : LoFExpr0)) :
    stabilizesAt_sig 0 G := by
  simp [stabilizesAt_sig, sigProfile, h]

theorem eventualStabilizes_sig_of_void {G : CoGame} (h : oscillationExpr G = (.void : LoFExpr0)) :
    eventualStabilizes_sig G := by
  exact ⟨0, stabilizesAt_sig_zero_of_void h⟩

theorem stabilizesAt_nucleus_zero_of_void {G : CoGame} (h : oscillationExpr G = (.void : LoFExpr0)) :
    stabilizesAt_nucleus 0 G := by
  simp [stabilizesAt_nucleus, supportProfile, sigProfile, h, collapseNucleus_apply]

theorem eventualStabilizes_nucleus_of_void {G : CoGame} (h : oscillationExpr G = (.void : LoFExpr0)) :
    eventualStabilizes_nucleus G := by
  exact ⟨0, stabilizesAt_nucleus_zero_of_void h⟩

theorem sigProfile_ne_succ_of_reentry {G : CoGame} (h : oscillationExpr G = .reentry) :
    ∀ n : Nat, sigProfile (Nat.succ n) G ≠ sigProfile n G
  | 0 => by
      simp [sigProfile, h]
  | Nat.succ n => by
      intro hEq
      have hEq' : sigProfile (Nat.succ n) G = sigProfile n G := by
        have hEqMark :
            HeytingLean.LoF.LoFSecond.Expr.mark (sigProfile (Nat.succ n) G)
              = HeytingLean.LoF.LoFSecond.Expr.mark (sigProfile n G) := by
          simpa [sigProfile, h] using hEq
        injection hEqMark with hInner
      exact (sigProfile_ne_succ_of_reentry h n) hEq'

theorem not_eventualStabilizes_sig_of_reentry {G : CoGame} (h : oscillationExpr G = .reentry) :
    ¬ eventualStabilizes_sig G := by
  intro hs
  rcases hs with ⟨n, hn⟩
  exact (sigProfile_ne_succ_of_reentry h n) hn

theorem supportProfile_singleton_of_reentry {G : CoGame} (h : oscillationExpr G = .reentry) :
    ∀ n : Nat, supportProfile n G = ({n} : Set Nat)
  | 0 => by
      simp [supportProfile, sigProfile, h, exprSupport]
  | Nat.succ n => by
      calc
        supportProfile (Nat.succ n) G
            = Nat.succ '' supportProfile n G := by
              simp [supportProfile, sigProfile, h, exprSupport]
        _ = Nat.succ '' ({n} : Set Nat) := by
              simp [supportProfile_singleton_of_reentry h n]
        _ = ({Nat.succ n} : Set Nat) := by
              ext x
              constructor
              · intro hx
                rcases hx with ⟨y, hy, rfl⟩
                simp at hy
                simp [hy]
              · intro hx
                simp at hx
                rcases hx with rfl
                refine ⟨n, ?_, rfl⟩
                simp

theorem not_stabilizesAt_nucleus_of_reentry {G : CoGame} (h : oscillationExpr G = .reentry) :
    ∀ n : Nat, ¬ stabilizesAt_nucleus n G
  | n => by
      intro hn
      have hmemL : Nat.succ n ∈ collapseNucleus (supportProfile (Nat.succ n) G) := by
        change Nat.succ n ∈ supportProfile (Nat.succ n) G ∪ ({0} : Set Nat)
        refine Or.inl ?_
        simp [supportProfile_singleton_of_reentry h (Nat.succ n)]
      have hmemR : Nat.succ n ∈ collapseNucleus (supportProfile n G) := by
        exact hn ▸ hmemL
      have hmemR' : Nat.succ n ∈ ({n} : Set Nat) ∪ ({0} : Set Nat) := by
        have htmp := hmemR
        simp [collapseNucleus_apply, supportProfile_singleton_of_reentry h n] at htmp
      have : Nat.succ n = n ∨ Nat.succ n = 0 := by
        have htmp := hmemR'
        simp at htmp
      cases this with
      | inl hEq =>
          exact (Nat.succ_ne_self n) hEq
      | inr hEq =>
          exact (Nat.succ_ne_zero n) hEq

theorem not_eventualStabilizes_nucleus_of_reentry {G : CoGame} (h : oscillationExpr G = .reentry) :
    ¬ eventualStabilizes_nucleus G := by
  intro hs
  rcases hs with ⟨n, hn⟩
  exact (not_stabilizesAt_nucleus_of_reentry h n) hn

theorem eventualStabilizes_sig_iff_nucleus (G : CoGame) :
    eventualStabilizes_sig G ↔ eventualStabilizes_nucleus G := by
  rcases oscillationExpr_cases G with hVoid | hRe
  · constructor
    · intro _hs
      exact eventualStabilizes_nucleus_of_void hVoid
    · intro _hn
      exact eventualStabilizes_sig_of_void hVoid
  · constructor
    · intro hs
      exact False.elim ((not_eventualStabilizes_sig_of_reentry hRe) hs)
    · intro hn
      exact False.elim ((not_eventualStabilizes_nucleus_of_reentry hRe) hn)

theorem eventualStabilizes_iff_sig (G : CoGame) :
    eventualStabilizes G ↔ eventualStabilizes_sig G := by
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, (eventualStabilizes_sig_iff_nucleus G).1 h⟩

theorem eventualStabilizes_iff_nucleus (G : CoGame) :
    eventualStabilizes G ↔ eventualStabilizes_nucleus G := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨(eventualStabilizes_sig_iff_nucleus G).2 h, h⟩

theorem void_eventualStabilizes : eventualStabilizes CoGame.Void := by
  refine ⟨?_, ?_⟩
  · exact eventualStabilizes_sig_of_void (by simp [oscillationExpr_void])
  · exact eventualStabilizes_nucleus_of_void (by simp [oscillationExpr_void])

theorem life_not_eventualStabilizes : ¬ eventualStabilizes CoGame.Life := by
  intro h
  exact (not_eventualStabilizes_sig_of_reentry (by simp [oscillationExpr_life])) h.1

end HeytingLean.Genesis
