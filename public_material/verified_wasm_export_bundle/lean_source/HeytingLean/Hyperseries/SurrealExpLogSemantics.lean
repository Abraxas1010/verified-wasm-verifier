import HeytingLean.Hyperseries.ModelLaws
import Mathlib.SetTheory.Ordinal.Arithmetic

namespace HeytingLean
namespace Hyperseries

/--
Internal semantics package for surreal exp/log and hyper-operators.
This is the staged replacement surface for identity placeholders.
-/
structure SurrealExpLogCore where
  exp : Surreal → Surreal
  log : Surreal → Surreal
  exp_log : ∀ x : Surreal, exp (log x) = x
  log_exp : ∀ x : Surreal, log (exp x) = x

structure SurrealExpLogSemantics where
  exp : Surreal → Surreal
  log : Surreal → Surreal
  hyperExp : Ordinal → Surreal → Surreal
  hyperLog : Ordinal → Surreal → Surreal
  exp_log : ∀ x : Surreal, exp (log x) = x
  log_exp : ∀ x : Surreal, log (exp x) = x
  hyperExp_zero : ∀ x : Surreal, hyperExp 0 x = exp x
  hyperLog_zero : ∀ x : Surreal, hyperLog 0 x = log x
  hyperExp_succ : ∀ α : Ordinal, ∀ x : Surreal, hyperExp (Order.succ α) x = exp (hyperExp α x)
  hyperLog_succ : ∀ α : Ordinal, ∀ x : Surreal, hyperLog (Order.succ α) x = log (hyperLog α x)

namespace SurrealExpLogSemantics

/-- Forget hyper-operators and keep only the exp/log core. -/
def toCore (S : SurrealExpLogSemantics) : SurrealExpLogCore where
  exp := S.exp
  log := S.log
  exp_log := S.exp_log
  log_exp := S.log_exp

/--
Extend an exp/log core to full surreal hyperserial semantics by supplying
hyper-operators and their coherence laws.
-/
def ofCore (C : SurrealExpLogCore)
    (hyperExp hyperLog : Ordinal → Surreal → Surreal)
    (hyperExp_zero : ∀ x : Surreal, hyperExp 0 x = C.exp x)
    (hyperLog_zero : ∀ x : Surreal, hyperLog 0 x = C.log x)
    (hyperExp_succ : ∀ α : Ordinal, ∀ x : Surreal, hyperExp (Order.succ α) x = C.exp (hyperExp α x))
    (hyperLog_succ : ∀ α : Ordinal, ∀ x : Surreal, hyperLog (Order.succ α) x = C.log (hyperLog α x)) :
    SurrealExpLogSemantics where
  exp := C.exp
  log := C.log
  hyperExp := hyperExp
  hyperLog := hyperLog
  exp_log := C.exp_log
  log_exp := C.log_exp
  hyperExp_zero := hyperExp_zero
  hyperLog_zero := hyperLog_zero
  hyperExp_succ := hyperExp_succ
  hyperLog_succ := hyperLog_succ

/--
Canonical transfinite iterator from a core unary operation.
Successor ordinals apply one more step; limit ordinals fall back to the base.
-/
noncomputable def iterateFrom (f : Surreal → Surreal) (base : Surreal) : Ordinal → Surreal :=
  fun α =>
    Ordinal.limitRecOn α base
      (fun _ y => f y)
      (fun _ _ _ => base)

@[simp] theorem iterateFrom_zero (f : Surreal → Surreal) (base : Surreal) :
    iterateFrom f base 0 = base := by
  simp [iterateFrom]

@[simp] theorem iterateFrom_succ (f : Surreal → Surreal) (base : Surreal) (α : Ordinal) :
    iterateFrom f base (Order.succ α) = f (iterateFrom f base α) := by
  simp [iterateFrom, Ordinal.limitRecOn_succ]

/-- Hyper-exp lane induced canonically from an exp/log core. -/
noncomputable def hyperExpFromCore (C : SurrealExpLogCore) : Ordinal → Surreal → Surreal :=
  fun α x => iterateFrom C.exp (C.exp x) α

/-- Hyper-log lane induced canonically from an exp/log core. -/
noncomputable def hyperLogFromCore (C : SurrealExpLogCore) : Ordinal → Surreal → Surreal :=
  fun α x => iterateFrom C.log (C.log x) α

@[simp] theorem hyperExpFromCore_zero (C : SurrealExpLogCore) (x : Surreal) :
    hyperExpFromCore C 0 x = C.exp x := by
  simp [hyperExpFromCore]

@[simp] theorem hyperLogFromCore_zero (C : SurrealExpLogCore) (x : Surreal) :
    hyperLogFromCore C 0 x = C.log x := by
  simp [hyperLogFromCore]

@[simp] theorem hyperExpFromCore_succ (C : SurrealExpLogCore) (α : Ordinal) (x : Surreal) :
    hyperExpFromCore C (Order.succ α) x = C.exp (hyperExpFromCore C α x) := by
  simp [hyperExpFromCore]

@[simp] theorem hyperLogFromCore_succ (C : SurrealExpLogCore) (α : Ordinal) (x : Surreal) :
    hyperLogFromCore C (Order.succ α) x = C.log (hyperLogFromCore C α x) := by
  simp [hyperLogFromCore]

/--
Canonical full semantics induced from an exp/log core by ordinal iteration.
-/
noncomputable def ofCoreIterated (C : SurrealExpLogCore) : SurrealExpLogSemantics :=
  ofCore C (hyperExpFromCore C) (hyperLogFromCore C)
    (hyperExpFromCore_zero C)
    (hyperLogFromCore_zero C)
    (hyperExpFromCore_succ C)
    (hyperLogFromCore_succ C)

/-- Convert a semantics package into a `HyperserialModel` on `Surreal`. -/
noncomputable def toModel (S : SurrealExpLogSemantics) : HyperserialModel Surreal where
  omega := omegaSurreal
  exp := S.exp
  log := S.log
  hyperExp := S.hyperExp
  hyperLog := S.hyperLog

/-- Any packaged semantics carries the full `HyperserialModelLaws` layer. -/
noncomputable instance instModelLaws (S : SurrealExpLogSemantics) :
    HyperserialModelLaws Surreal (toModel S) where
  exp_log := S.exp_log
  log_exp := S.log_exp
  hyperExp_zero := S.hyperExp_zero
  hyperLog_zero := S.hyperLog_zero
  hyperExp_succ := S.hyperExp_succ
  hyperLog_succ := S.hyperLog_succ

/--
Optional nontriviality marker used to distinguish real semantics from
the identity fallback.
-/
def Nontrivial (S : SurrealExpLogSemantics) : Prop :=
  ∃ x : Surreal, S.exp x ≠ x ∨ S.log x ≠ x

/-- Core-level nontriviality marker (ignoring hyper-operator choices). -/
def CoreNontrivial (C : SurrealExpLogCore) : Prop :=
  ∃ x : Surreal, C.exp x ≠ x ∨ C.log x ≠ x

/-- A non-identity exp/log core: involution by additive inverse. -/
def negCore : SurrealExpLogCore where
  exp := fun x => -x
  log := fun x => -x
  exp_log x := by simp
  log_exp x := by simp

theorem coreNontrivial_negCore : CoreNontrivial negCore := by
  refine ⟨(1 : Surreal), ?_⟩
  left
  intro h
  have hneg : (- (1 : Surreal)) = (1 : Surreal) := by
    simpa [negCore] using h
  have hzero : (1 : Surreal) + (1 : Surreal) = 0 := by
    calc
      (1 : Surreal) + (1 : Surreal) = (- (1 : Surreal)) + (1 : Surreal) := by
        exact congrArg (fun t => t + (1 : Surreal)) hneg.symm
      _ = 0 := by simp
  have htwo' : (2 : Surreal) = (1 : Surreal) + (1 : Surreal) := by
    norm_num
  have htwo : (2 : Surreal) = 0 := by
    calc
      (2 : Surreal) = (1 : Surreal) + (1 : Surreal) := htwo'
      _ = 0 := hzero
  exact two_ne_zero htwo

/-- Non-identity full semantics induced from `negCore` by canonical iteration. -/
noncomputable def negSemantics : SurrealExpLogSemantics :=
  ofCoreIterated negCore

theorem nontrivial_negSemantics : Nontrivial negSemantics := by
  refine ⟨(1 : Surreal), ?_⟩
  left
  intro h
  have hneg : (-(1 : Surreal)) = (1 : Surreal) := by
    simpa [negSemantics, ofCoreIterated, ofCore, negCore] using h
  have hzero : (1 : Surreal) + (1 : Surreal) = 0 := by
    calc
      (1 : Surreal) + (1 : Surreal) = (-(1 : Surreal)) + (1 : Surreal) := by
        exact congrArg (fun t => t + (1 : Surreal)) hneg.symm
      _ = 0 := by simp
  have htwo : (2 : Surreal) = 0 := by
    calc
      (2 : Surreal) = (1 : Surreal) + (1 : Surreal) := by norm_num
      _ = 0 := hzero
  exact two_ne_zero htwo

/-- Identity fallback package aligned with the current pinned implementation. -/
noncomputable def identity : SurrealExpLogSemantics where
  exp := fun x => x
  log := fun x => x
  hyperExp := fun _ x => x
  hyperLog := fun _ x => x
  exp_log _ := rfl
  log_exp _ := rfl
  hyperExp_zero _ := rfl
  hyperLog_zero _ := rfl
  hyperExp_succ _ _ := rfl
  hyperLog_succ _ _ := rfl

/-- Current selected default semantics package. -/
noncomputable def default : SurrealExpLogSemantics :=
  identity

/--
Optional selector for staged integration work:
`false` keeps the identity/default package, `true` enables the nontrivial
`negSemantics` package.
-/
noncomputable def select (useNontrivial : Bool) : SurrealExpLogSemantics :=
  if useNontrivial then negSemantics else default

/--
Explicit placeholder semantics lane (currently the identity package),
kept separate from `default` so downstream code can target placeholder
behavior even if `default` changes later.
-/
noncomputable def placeholder : SurrealExpLogSemantics :=
  identity

@[simp] theorem placeholder_eq_select_false :
    placeholder = select false := rfl

@[simp] theorem placeholder_eq_default :
    placeholder = default := by
  rfl

/--
Active semantics lane used by the executable hyperseries pipeline.
This currently points to `placeholder`; switching to a nontrivial lane
should happen by updating this definition only.
-/
def activeUseNontrivial : Bool := false

@[simp] theorem activeUseNontrivial_eq_false :
    activeUseNontrivial = false := rfl

noncomputable def active : SurrealExpLogSemantics :=
  select activeUseNontrivial

@[simp] theorem active_eq_select :
    active = select activeUseNontrivial := rfl

@[simp] theorem active_eq_select_false :
    active = select false := by
  simp [active, activeUseNontrivial]

@[simp] theorem active_eq_placeholder :
    active = placeholder := by
  simp [active, activeUseNontrivial, placeholder, select, default, identity]

@[simp] theorem active_eq_default :
    active = default := by
  exact active_eq_placeholder.trans placeholder_eq_default

@[simp] theorem select_false : select false = default := by
  simp [select]

@[simp] theorem select_true : select true = negSemantics := by
  simp [select]

@[simp] theorem negSemantics_exp (x : Surreal) :
    negSemantics.exp x = -x := by
  rfl

@[simp] theorem negSemantics_log (x : Surreal) :
    negSemantics.log x = -x := by
  rfl

@[simp] theorem negSemantics_hyperExp_zero (x : Surreal) :
    negSemantics.hyperExp 0 x = -x := by
  simp [negSemantics, ofCoreIterated, ofCore, negCore]

@[simp] theorem negSemantics_hyperLog_zero (x : Surreal) :
    negSemantics.hyperLog 0 x = -x := by
  simp [negSemantics, ofCoreIterated, ofCore, negCore]

@[simp] theorem negSemantics_hyperExp_succ (α : Ordinal) (x : Surreal) :
    negSemantics.hyperExp (Order.succ α) x = -(negSemantics.hyperExp α x) := by
  simp [negSemantics, ofCoreIterated, ofCore, negCore]

@[simp] theorem negSemantics_hyperLog_succ (α : Ordinal) (x : Surreal) :
    negSemantics.hyperLog (Order.succ α) x = -(negSemantics.hyperLog α x) := by
  simp [negSemantics, ofCoreIterated, ofCore, negCore]

@[simp] theorem select_false_exp (x : Surreal) :
    (select false).exp x = x := by
  simp [select, default, identity]

@[simp] theorem select_false_log (x : Surreal) :
    (select false).log x = x := by
  simp [select, default, identity]

@[simp] theorem select_false_hyperExp (α : Ordinal) (x : Surreal) :
    (select false).hyperExp α x = x := by
  simp [select, default, identity]

@[simp] theorem select_false_hyperLog (α : Ordinal) (x : Surreal) :
    (select false).hyperLog α x = x := by
  simp [select, default, identity]

@[simp] theorem select_true_exp (x : Surreal) :
    (select true).exp x = -x := by
  simp [select]

@[simp] theorem select_true_log (x : Surreal) :
    (select true).log x = -x := by
  simp [select]

@[simp] theorem select_true_hyperExp_zero (x : Surreal) :
    (select true).hyperExp 0 x = -x := by
  simp [select]

@[simp] theorem select_true_hyperLog_zero (x : Surreal) :
    (select true).hyperLog 0 x = -x := by
  simp [select]

theorem nontrivial_select_true : Nontrivial (select true) := by
  simpa [select] using nontrivial_negSemantics

theorem not_nontrivial_select_false : ¬Nontrivial (select false) := by
  intro h
  rcases h with ⟨x, hx | hx⟩
  · exact hx (by simp [select, default, identity])
  · exact hx (by simp [select, default, identity])

theorem not_nontrivial_placeholder : ¬Nontrivial placeholder := by
  simpa [placeholder] using not_nontrivial_select_false

theorem nontrivial_select_iff (b : Bool) :
    Nontrivial (select b) ↔ b = true := by
  cases b with
  | false =>
      constructor
      · intro h
        exact False.elim (not_nontrivial_select_false h)
      · intro h
        cases h
  | true =>
      constructor
      · intro _
        rfl
      · intro _
        exact nontrivial_select_true

theorem not_nontrivial_select_iff (b : Bool) :
    ¬Nontrivial (select b) ↔ b = false := by
  cases b with
  | false =>
      constructor
      · intro _
        rfl
      · intro _
        exact not_nontrivial_select_false
  | true =>
      constructor
      · intro h
        exact False.elim (h nontrivial_select_true)
      · intro h
        cases h

theorem nontrivial_active_iff :
    Nontrivial active ↔ activeUseNontrivial = true := by
  simpa [active] using nontrivial_select_iff activeUseNontrivial

theorem not_nontrivial_active_iff :
    ¬Nontrivial active ↔ activeUseNontrivial = false := by
  simpa [active] using not_nontrivial_select_iff activeUseNontrivial

theorem not_nontrivial_active : ¬Nontrivial active := by
  simpa [activeUseNontrivial] using (not_nontrivial_active_iff.2 rfl)

theorem active_ne_select_true : active ≠ select true := by
  intro h
  exact not_nontrivial_active (h ▸ nontrivial_select_true)

/-- Model induced by the currently selected default semantics package. -/
noncomputable abbrev defaultModel : HyperserialModel Surreal :=
  toModel default

/-- Model induced by the explicit placeholder semantics lane. -/
noncomputable abbrev placeholderModel : HyperserialModel Surreal :=
  toModel placeholder

/-- Model induced by the active semantics lane. -/
noncomputable abbrev activeModel : HyperserialModel Surreal :=
  toModel active

@[simp] theorem toModel_select_false_exp (x : Surreal) :
    (toModel (select false)).exp x = x := by
  simp [select, default, identity, toModel]

@[simp] theorem toModel_select_false_log (x : Surreal) :
    (toModel (select false)).log x = x := by
  simp [select, default, identity, toModel]

@[simp] theorem toModel_select_false_hyperExp (α : Ordinal) (x : Surreal) :
    (toModel (select false)).hyperExp α x = x := by
  simp [select, default, identity, toModel]

@[simp] theorem toModel_select_false_hyperLog (α : Ordinal) (x : Surreal) :
    (toModel (select false)).hyperLog α x = x := by
  simp [select, default, identity, toModel]

@[simp] theorem toModel_placeholder_exp (x : Surreal) :
    (toModel placeholder).exp x = x := by
  simp [placeholder, identity, toModel]

@[simp] theorem toModel_placeholder_log (x : Surreal) :
    (toModel placeholder).log x = x := by
  simp [placeholder, identity, toModel]

@[simp] theorem toModel_placeholder_hyperExp (α : Ordinal) (x : Surreal) :
    (toModel placeholder).hyperExp α x = x := by
  simp [placeholder, identity, toModel]

@[simp] theorem toModel_placeholder_hyperLog (α : Ordinal) (x : Surreal) :
    (toModel placeholder).hyperLog α x = x := by
  simp [placeholder, identity, toModel]

@[simp] theorem toModel_active_exp (x : Surreal) :
    HyperserialModel.exp (self := toModel active) x = x := by
  simp [active, activeUseNontrivial, toModel]

@[simp] theorem toModel_active_log (x : Surreal) :
    HyperserialModel.log (self := toModel active) x = x := by
  simp [active, activeUseNontrivial, toModel]

@[simp] theorem toModel_active_hyperExp (α : Ordinal) (x : Surreal) :
    HyperserialModel.hyperExp (self := toModel active) α x = x := by
  simp [active, activeUseNontrivial, toModel]

@[simp] theorem toModel_active_hyperLog (α : Ordinal) (x : Surreal) :
    HyperserialModel.hyperLog (self := toModel active) α x = x := by
  simp [active, activeUseNontrivial, toModel]

@[simp] theorem toModel_select_true_exp (x : Surreal) :
    (toModel (select true)).exp x = -x := by
  simp [select, toModel]

@[simp] theorem toModel_select_true_log (x : Surreal) :
    (toModel (select true)).log x = -x := by
  simp [select, toModel]

@[simp] theorem toModel_select_true_hyperExp_zero (x : Surreal) :
    (toModel (select true)).hyperExp 0 x = -x := by
  simp [select, toModel, negSemantics, ofCoreIterated, ofCore, negCore]

@[simp] theorem toModel_select_true_hyperLog_zero (x : Surreal) :
    (toModel (select true)).hyperLog 0 x = -x := by
  simp [select, toModel, negSemantics, ofCoreIterated, ofCore, negCore]

@[simp] theorem toModel_select_true_hyperExp_succ (α : Ordinal) (x : Surreal) :
    (toModel (select true)).hyperExp (Order.succ α) x =
      -((toModel (select true)).hyperExp α x) := by
  simp [select, toModel, negSemantics, ofCoreIterated, ofCore, negCore]

@[simp] theorem toModel_select_true_hyperLog_succ (α : Ordinal) (x : Surreal) :
    (toModel (select true)).hyperLog (Order.succ α) x =
      -((toModel (select true)).hyperLog α x) := by
  simp [select, toModel, negSemantics, ofCoreIterated, ofCore, negCore]

@[simp] theorem toModel_identity_exp (x : Surreal) :
    (toModel identity).exp x = x := rfl

@[simp] theorem toModel_identity_log (x : Surreal) :
    (toModel identity).log x = x := rfl

@[simp] theorem toModel_identity_hyperExp (α : Ordinal) (x : Surreal) :
    (toModel identity).hyperExp α x = x := rfl

@[simp] theorem toModel_identity_hyperLog (α : Ordinal) (x : Surreal) :
    (toModel identity).hyperLog α x = x := rfl

theorem not_nontrivial_identity : ¬Nontrivial identity := by
  intro h
  rcases h with ⟨x, hx | hx⟩
  · exact hx rfl
  · exact hx rfl

theorem toCore_identity : toCore identity = {
    exp := fun x => x
    log := fun x => x
    exp_log := fun _ => rfl
    log_exp := fun _ => rfl
  } := rfl

end SurrealExpLogSemantics

end Hyperseries
end HeytingLean
