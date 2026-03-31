import HeytingLean.Genesis.Observer

/-!
# Genesis.ObserverV2

Phase-11 observer extension:
- constraint state over completed trajectories,
- bounded (finite-prefix) update discipline,
- v1 compatibility preservation.
-/

namespace HeytingLean.Genesis

/-- Constraint state for completed-observer trajectories. -/
structure ConstraintState where
  decideAt : Nat → Option Bool

namespace ConstraintState

/-- Empty constraint state. -/
def empty : ConstraintState where
  decideAt := fun _ => none

/-- Update a single coordinate with a concrete Boolean assignment. -/
def assign (σ : ConstraintState) (n : Nat) (b : Bool) : ConstraintState where
  decideAt := fun k => if k = n then some b else σ.decideAt k

@[simp] theorem assign_eq (σ : ConstraintState) (n : Nat) (b : Bool) :
    (assign σ n b).decideAt n = some b := by
  simp [assign]

@[simp] theorem assign_ne (σ : ConstraintState) {n k : Nat} (b : Bool) (hkn : k ≠ n) :
    (assign σ n b).decideAt k = σ.decideAt k := by
  simp [assign, hkn]

@[ext] theorem ext {σ τ : ConstraintState}
    (h : ∀ n, σ.decideAt n = τ.decideAt n) : σ = τ := by
  cases σ with
  | mk f =>
      cases τ with
      | mk g =>
          have hfg : f = g := funext h
          cases hfg
          rfl

/-- Compatibility between constraints and a completed observer trajectory. -/
def agrees (σ : ConstraintState) (p : CompletedObserver) : Prop :=
  ∀ n b, σ.decideAt n = some b → p n = b

theorem empty_agrees (p : CompletedObserver) : agrees empty p := by
  intro n b h
  simp [empty] at h

theorem agrees_assign {σ : ConstraintState} {p : CompletedObserver}
    (hσ : agrees σ p) {n : Nat} {b : Bool} (hpb : p n = b) :
    agrees (assign σ n b) p := by
  intro k c hk
  by_cases hkn : k = n
  · subst hkn
    simp [assign] at hk
    subst hk
    exact hpb
  · have hσk : σ.decideAt k = some c := by
      simpa [assign, hkn] using hk
    exact hσ k c hσk

theorem assign_idempotent (σ : ConstraintState) (n : Nat) (b : Bool) :
    assign (assign σ n b) n b = assign σ n b := by
  ext k
  by_cases hkn : k = n
  · subst hkn
    simp
  · simp [assign, hkn]

end ConstraintState

/-- Observer v2 keeps v1 payload and adds a constraint state. -/
structure ObserverV2 where
  base : Observer
  constraints : ConstraintState

/-- Canonical constraint state induced by a finite observer prefix. -/
def constraintsOfObserver (o : Observer) : ConstraintState where
  decideAt := fun n =>
    if h : n < o.depth then some (o.choices ⟨n, h⟩) else none

theorem constraintsOfObserver_agrees_defaultCompletion (o : Observer) :
    ConstraintState.agrees (constraintsOfObserver o) (defaultCompletion o) := by
  intro n b hnb
  by_cases hn : n < o.depth
  · have hchoice : some (o.choices ⟨n, hn⟩) = some b := by
      simpa [constraintsOfObserver, hn] using hnb
    have hb : o.choices ⟨n, hn⟩ = b := Option.some.inj hchoice
    simp [defaultCompletion, hn, hb]
  · have : (constraintsOfObserver o).decideAt n = none := by
      simp [constraintsOfObserver, hn]
    rw [this] at hnb
    cases hnb

/-- Lift a v1 observer into v2 with canonical constraints. -/
def ObserverV2.fromObserver (o : Observer) : ObserverV2 where
  base := o
  constraints := constraintsOfObserver o

/-- Forgetful projection from v2 to v1. -/
abbrev ObserverV2.toObserver (O : ObserverV2) : Observer := O.base

@[simp] theorem fromObserver_toObserver (o : Observer) :
    (ObserverV2.fromObserver o).toObserver = o := rfl

/-- Bounded update: reinforce an already-observed finite choice. -/
def reinforceChoice (O : ObserverV2) (i : Fin O.base.depth) : ObserverV2 where
  base := O.base
  constraints := ConstraintState.assign O.constraints i.1 (O.base.choices i)

/-- Reinforcing an observed finite prefix preserves compatibility with default completion. -/
theorem reinforceChoice_preserves_defaultCompletion
    (O : ObserverV2)
    (hO : ConstraintState.agrees O.constraints (defaultCompletion O.base))
    (i : Fin O.base.depth) :
    ConstraintState.agrees (reinforceChoice O i).constraints (defaultCompletion O.base) := by
  apply ConstraintState.agrees_assign hO
  simp [defaultCompletion, i.is_lt]

/-- Level-2 transfinite-growth placeholder, explicitly extension-scoped. -/
structure Level2GrowthPlan where
  seed : ObserverV2
  nextConstraint : Nat → ConstraintState
  invariantsRecorded : ∀ _n : Nat, True

/-- Explicit marker that level>1 tower growth is future extension work. -/
def level2_extension_note : String :=
  "Level>1 transfinite observer growth remains extension-scoped; implement after interface hardening."

end HeytingLean.Genesis
