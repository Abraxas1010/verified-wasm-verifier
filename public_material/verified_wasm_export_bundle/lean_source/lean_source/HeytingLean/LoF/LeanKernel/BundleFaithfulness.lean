import HeytingLean.LoF.LeanKernel.BundleSchema
import HeytingLean.LoF.LeanKernel.BundleCheck
import HeytingLean.LoF.LeanKernel.Infer

/-!
# LeanKernel.BundleFaithfulness (Phase 1 — Kernel Assurance Bridge)

Defines the *supported fragment* for the kernel assurance top semantic bridge and
states the faithfulness obligations for the bundle export pipeline.
-/

namespace HeytingLean
namespace LoF
namespace LeanKernel

namespace BundleFaithfulness

open HeytingLean.LoF.LeanKernel

/-- A universe level is *supported* if it contains no metavariables. -/
def SupportedLevel : SLevel → Prop
  | .zero => True
  | .succ u => SupportedLevel u
  | .max a b => SupportedLevel a ∧ SupportedLevel b
  | .imax a b => SupportedLevel a ∧ SupportedLevel b
  | .param _ => True
  | .mvar _ => False

/-- Boolean decision procedure for `SupportedLevel`. -/
def supportedLevelBool : SLevel → Bool
  | .zero => true
  | .succ u => supportedLevelBool u
  | .max a b => supportedLevelBool a && supportedLevelBool b
  | .imax a b => supportedLevelBool a && supportedLevelBool b
  | .param _ => true
  | .mvar _ => false

/-- `supportedLevelBool` reflects `SupportedLevel`. -/
theorem supportedLevelBool_iff (u : SLevel) :
    supportedLevelBool u = true ↔ SupportedLevel u := by
  induction u with
  | zero => simp [supportedLevelBool, SupportedLevel]
  | succ u ih => simp [supportedLevelBool, SupportedLevel, ih]
  | max a b iha ihb => simp [supportedLevelBool, SupportedLevel, Bool.and_eq_true, iha, ihb]
  | imax a b iha ihb => simp [supportedLevelBool, SupportedLevel, Bool.and_eq_true, iha, ihb]
  | param _ => simp [supportedLevelBool, SupportedLevel]
  | mvar _ => simp [supportedLevelBool, SupportedLevel]

instance (u : SLevel) : Decidable (SupportedLevel u) :=
  if h : supportedLevelBool u = true then
    isTrue ((supportedLevelBool_iff u).mp h)
  else
    isFalse (fun hs => h ((supportedLevelBool_iff u).mpr hs))

/-- An expression is *supported* if it contains no expression-level metavariables
and all universe levels are supported. -/
def SupportedExpr : SExpr → Prop
  | .bvar _ => True
  | .mvar _ => False
  | .sort u => SupportedLevel u
  | .const _ us => ∀ u ∈ us, SupportedLevel u
  | .app f a => SupportedExpr f ∧ SupportedExpr a
  | .lam _ _ ty body => SupportedExpr ty ∧ SupportedExpr body
  | .forallE _ _ ty body => SupportedExpr ty ∧ SupportedExpr body
  | .letE _ _ ty val body => SupportedExpr ty ∧ SupportedExpr val ∧ SupportedExpr body
  | .lit _ => True

/-- Boolean decision procedure for `SupportedExpr`. -/
def supportedExprBool : SExpr → Bool
  | .bvar _ => true
  | .mvar _ => false
  | .sort u => supportedLevelBool u
  | .const _ us => us.all supportedLevelBool
  | .app f a => supportedExprBool f && supportedExprBool a
  | .lam _ _ ty body => supportedExprBool ty && supportedExprBool body
  | .forallE _ _ ty body => supportedExprBool ty && supportedExprBool body
  | .letE _ _ ty val body => supportedExprBool ty && supportedExprBool val && supportedExprBool body
  | .lit _ => true

/-- `supportedExprBool` reflects `SupportedExpr`. -/
theorem supportedExprBool_iff (e : SExpr) :
    supportedExprBool e = true ↔ SupportedExpr e := by
  induction e with
  | bvar _ => simp [supportedExprBool, SupportedExpr]
  | mvar _ => simp [supportedExprBool, SupportedExpr]
  | sort u => simp [supportedExprBool, SupportedExpr, supportedLevelBool_iff]
  | const _ us =>
    simp only [supportedExprBool, SupportedExpr]
    rw [List.all_eq_true]
    exact forall₂_congr (fun u _ => supportedLevelBool_iff u)
  | app f a ihf iha => simp [supportedExprBool, SupportedExpr, Bool.and_eq_true, ihf, iha]
  | lam _ _ ty body iht ihb => simp [supportedExprBool, SupportedExpr, Bool.and_eq_true, iht, ihb]
  | forallE _ _ ty body iht ihb => simp [supportedExprBool, SupportedExpr, Bool.and_eq_true, iht, ihb]
  | letE _ _ ty val body iht ihv ihb =>
    simp only [supportedExprBool, SupportedExpr, Bool.and_eq_true]
    exact ⟨fun ⟨⟨ht, hv⟩, hb⟩ => ⟨iht.mp ht, ihv.mp hv, ihb.mp hb⟩,
           fun ⟨ht, hv, hb⟩ => ⟨⟨iht.mpr ht, ihv.mpr hv⟩, ihb.mpr hb⟩⟩
  | lit _ => simp [supportedExprBool, SupportedExpr]

instance (e : SExpr) : Decidable (SupportedExpr e) :=
  if h : supportedExprBool e = true then
    isTrue ((supportedExprBool_iff e).mp h)
  else
    isFalse (fun hs => h ((supportedExprBool_iff e).mpr hs))

/-- A bundle is *supported* if the exporter completed without degradation. -/
structure SupportedBundle (b : ArbitraryLeanKernelBundle) : Prop where
  no_overflow : b.closureOverflow = false
  no_erased_levels : b.erasedUniversePayload = false
  no_erased_metas : b.erasedExprMetas = false
  no_missing_deps : b.missingDeps.isEmpty = true
  obligations_supported : ∀ o ∈ b.obligations, SupportedExpr o.expr ∧
    (∀ e2 ∈ o.expr2?, SupportedExpr e2)
  target_supported : SupportedExpr b.targetType
  target_value_supported : ∀ v ∈ b.targetValue?, SupportedExpr v

/-- Configuration derived from a bundle via `bundleToEnv` + `toInferConfig`. -/
def bundleConfig (b : ArbitraryLeanKernelBundle) : Infer.Config Nat Nat Nat Nat :=
  (bundleToEnv b).toInferConfig

/-- An obligation is *faithfully evaluated* at the given fuel. -/
def FaithfulObligation (b : ArbitraryLeanKernelBundle) (fuel : Nat)
    (o : KernelObligation) : Prop :=
  let cfg := bundleConfig b
  match o.kind with
  | .whnf => SupportedExpr o.expr
  | .infer => ∃ ty, Infer.infer? cfg fuel (Infer.Ctx.empty) o.expr = some ty
  | .inferSort => ∃ u, Infer.inferSort? cfg fuel (Infer.Ctx.empty) o.expr = some u
  | .check =>
      match o.expr2? with
      | some ty => Infer.check cfg fuel (Infer.Ctx.empty) o.expr ty = true
      | none => False
  | .defeq =>
      match o.expr2? with
      | some e2 => DefEq.isDefEqWithDelta cfg.constValue? cfg.iotaRules fuel o.expr e2 = true
      | none => False

/-- A bundle is *faithful at fuel `n`*. -/
def FaithfulBundle (b : ArbitraryLeanKernelBundle) (fuel : Nat) : Prop :=
  SupportedBundle b ∧ ∀ o ∈ b.obligations, FaithfulObligation b fuel o

/-! ## Identity substitution lemmas -/

/-- An assignment list `[(id, .param id)]` is an *identity assignment*:
it maps each parameter to itself. -/
def identityAssignments (ids : List Nat) : List (Nat × SLevel) :=
  ids.zip (ids.map ULevel.param)

/-- Empty assignment list is the identity on levels. -/
@[simp] theorem instantiateLevelParams_nil (u : SLevel) :
    instantiateLevelParams [] u = u := by
  cases u <;> simp [instantiateLevelParams]

/-- Empty assignment list is the identity on expressions. -/
@[simp] theorem instantiateExprLevelParams_nil (e : SExpr) :
    instantiateExprLevelParams [] e = e := by
  induction e with
  | bvar _ => simp [instantiateExprLevelParams]
  | mvar _ => simp [instantiateExprLevelParams]
  | sort u => simp [instantiateExprLevelParams, instantiateLevelParams_nil]
  | const c us =>
    simp only [instantiateExprLevelParams]
    congr 1
    induction us with
    | nil => rfl
    | cons u rest ih => simp [List.map, instantiateLevelParams_nil, ih]
  | app f a ihf iha => simp [instantiateExprLevelParams, ihf, iha]
  | lam _ _ ty body iht ihb => simp [instantiateExprLevelParams, iht, ihb]
  | forallE _ _ ty body iht ihb => simp [instantiateExprLevelParams, iht, ihb]
  | letE _ _ ty val body iht ihv ihb => simp [instantiateExprLevelParams, iht, ihv, ihb]
  | lit _ => simp [instantiateExprLevelParams]

/-- Empty level param IDs means no substitution. -/
@[simp] theorem instantiateWithLevels_nil_ids (us : List SLevel) (e : SExpr) :
    instantiateWithLevels [] us e = e := by
  simp [instantiateWithLevels, List.zip]

/-- Identity substitution spot-check: level zero with empty params. -/
theorem identity_subst_level_zero :
    instantiateLevelParams (identityAssignments []) (.zero : SLevel) = .zero := by
  simp [identityAssignments]

/-- Identity substitution spot-check: `bvar 0` with empty params. -/
theorem identity_subst_bvar :
    instantiateWithLevels [] [] (.bvar 0 : SExpr) = .bvar 0 := by
  simp [instantiateWithLevels]

/-! ## General identity substitution theorems -/

/-- `identityAssignments` distributes over cons. -/
@[simp] theorem identityAssignments_cons (id : Nat) (ids : List Nat) :
    identityAssignments (id :: ids) = (id, ULevel.param id) :: identityAssignments ids := by
  simp [identityAssignments, List.zip, List.map]

/-- Identity assignment on a param always returns `.param p`.
Proof: by induction on the assignment list; at each entry `(id, .param id)`,
either `p = id` (so we return `.param id = .param p`) or we continue. -/
theorem instantiateLevelParams_param_identity (ids : List Nat) (p : Nat) :
    instantiateLevelParams (identityAssignments ids) (.param p) = .param p := by
  induction ids with
  | nil => simp [identityAssignments]
  | cons id rest ih =>
    simp only [identityAssignments_cons, instantiateLevelParams]
    split
    · next h => exact congrArg ULevel.param (beq_iff_eq.mp h).symm
    · exact ih

/-- Helper: rewrap the cons form back to `identityAssignments` and apply IH. -/
private theorem id_level_step (id : Nat) (rest : List Nat) (u : SLevel)
    (ih : ∀ ids : List Nat, instantiateLevelParams (identityAssignments ids) u = u) :
    instantiateLevelParams ((id, ULevel.param id) :: identityAssignments rest) u = u := by
  rw [← identityAssignments_cons]; exact ih (id :: rest)

/-- **Identity substitution for levels** (unconditional):
`identityAssignments` maps each param `p` to `.param p`, so the
substitution is the identity on *all* levels — including `.mvar`. -/
theorem instantiateLevelParams_identity (ids : List Nat) (u : SLevel) :
    instantiateLevelParams (identityAssignments ids) u = u := by
  induction u generalizing ids with
  | param p => exact instantiateLevelParams_param_identity ids p
  | zero =>
    cases ids with
    | nil => simp [identityAssignments]
    | cons _ _ => simp [instantiateLevelParams]
  | mvar _ =>
    cases ids with
    | nil => simp [identityAssignments]
    | cons _ _ => simp [instantiateLevelParams]
  | succ u ih =>
    cases ids with
    | nil => simp [identityAssignments]
    | cons id rest =>
      simp only [identityAssignments_cons, instantiateLevelParams]
      congr 1; exact id_level_step id rest u ih
  | max a b iha ihb =>
    cases ids with
    | nil => simp [identityAssignments]
    | cons id rest =>
      simp only [identityAssignments_cons, instantiateLevelParams]
      have ha := id_level_step id rest a iha
      have hb := id_level_step id rest b ihb
      rw [ha, hb]
  | imax a b iha ihb =>
    cases ids with
    | nil => simp [identityAssignments]
    | cons id rest =>
      simp only [identityAssignments_cons, instantiateLevelParams]
      have ha := id_level_step id rest a iha
      have hb := id_level_step id rest b ihb
      rw [ha, hb]

/-- Helper: rewrap the cons form and apply IH for expressions. -/
private theorem id_expr_step (id : Nat) (rest : List Nat) (e : SExpr)
    (ih : ∀ ids : List Nat, instantiateExprLevelParams (identityAssignments ids) e = e) :
    instantiateExprLevelParams ((id, ULevel.param id) :: identityAssignments rest) e = e := by
  rw [← identityAssignments_cons]; exact ih (id :: rest)

/-- **Identity substitution for expressions** (unconditional):
since every universe-level parameter in the expression is mapped to itself,
the entire expression is unchanged. -/
theorem instantiateExprLevelParams_identity (ids : List Nat) (e : SExpr) :
    instantiateExprLevelParams (identityAssignments ids) e = e := by
  induction e generalizing ids with
  | bvar _ | mvar _ | lit _ =>
    cases ids with
    | nil => simp [identityAssignments]
    | cons _ _ => simp [instantiateExprLevelParams]
  | sort u =>
    cases ids with
    | nil => simp [identityAssignments]
    | cons id rest =>
      simp only [identityAssignments_cons, instantiateExprLevelParams]
      congr 1; exact id_level_step id rest u (fun ids => instantiateLevelParams_identity ids u)
  | const c us =>
    cases ids with
    | nil => simp [identityAssignments]
    | cons id rest =>
      simp only [identityAssignments_cons, instantiateExprLevelParams]
      congr 1
      induction us with
      | nil => rfl
      | cons u tail ihu =>
        simp only [List.map]
        rw [id_level_step id rest u (fun ids => instantiateLevelParams_identity ids u)]
        exact congrArg (u :: ·) ihu
  | app f a ihf iha =>
    cases ids with
    | nil => simp [identityAssignments]
    | cons id rest =>
      simp only [identityAssignments_cons, instantiateExprLevelParams]
      have hf := id_expr_step id rest f ihf
      have ha := id_expr_step id rest a iha
      rw [hf, ha]
  | lam _ _ ty body iht ihb =>
    cases ids with
    | nil => simp [identityAssignments]
    | cons id rest =>
      simp only [identityAssignments_cons, instantiateExprLevelParams]
      have ht := id_expr_step id rest ty iht
      have hb := id_expr_step id rest body ihb
      rw [ht, hb]
  | forallE _ _ ty body iht ihb =>
    cases ids with
    | nil => simp [identityAssignments]
    | cons id rest =>
      simp only [identityAssignments_cons, instantiateExprLevelParams]
      have ht := id_expr_step id rest ty iht
      have hb := id_expr_step id rest body ihb
      rw [ht, hb]
  | letE _ _ ty val body iht ihv ihb =>
    cases ids with
    | nil => simp [identityAssignments]
    | cons id rest =>
      simp only [identityAssignments_cons, instantiateExprLevelParams]
      have ht := id_expr_step id rest ty iht
      have hv := id_expr_step id rest val ihv
      have hb := id_expr_step id rest body ihb
      rw [ht, hv, hb]

/-- **Identity substitution via `instantiateWithLevels`**: mapping each
param id to `.param id` yields the original expression. This is the key
lemma for `EnvPreservesTypes` / `EnvPreservesValues`. -/
theorem instantiateWithLevels_identity (ids : List Nat) (e : SExpr) :
    instantiateWithLevels ids (ids.map ULevel.param) e = e := by
  simp only [instantiateWithLevels]
  exact instantiateExprLevelParams_identity ids e

/-! ## Environment preservation predicates -/

/-- For each `BundleConst`, `bundleToEnv` preserves the type at the identity
universe substitution. -/
def EnvPreservesTypes (b : ArbitraryLeanKernelBundle) : Prop :=
  let env := bundleToEnv b
  ∀ bc ∈ b.envConsts,
    env.constType? bc.nameId (bc.levelParamIds.map ULevel.param) = some bc.typeExpr

/-- For each valued `BundleConst`, `bundleToEnv` preserves the value. -/
def EnvPreservesValues (b : ArbitraryLeanKernelBundle) : Prop :=
  let env := bundleToEnv b
  ∀ bc ∈ b.envConsts, ∀ val ∈ bc.valueExpr?,
    env.constValue? bc.nameId (bc.levelParamIds.map ULevel.param) = some val

/-! ## Environment preservation proofs -/

/-- In a mapped list, `find?` returns the transform of the unique matching element. -/
private theorem find_mapped_envConst
    (consts : List BundleConst) (bc : BundleConst)
    (hbc : bc ∈ consts)
    (huniq : ∀ c ∈ consts, c.nameId = bc.nameId → c = bc)
    (transform : BundleConst → Environment.ConstDecl Nat Nat Nat Nat)
    (hname : ∀ c, (transform c).name = c.nameId) :
    (consts.map transform).find? (fun d => d.name == bc.nameId) = some (transform bc) := by
  induction consts with
  | nil => simp at hbc
  | cons hd tl ih =>
    rw [List.map, List.find?_cons, hname]
    rcases List.mem_cons.mp hbc with rfl | htl
    · simp [beq_self_eq_true]
    · by_cases h : hd.nameId == bc.nameId
      · have heq := huniq hd (List.mem_cons.mpr (Or.inl rfl)) (beq_iff_eq.mp h)
        rw [heq]; simp [beq_self_eq_true]
      · rw [show (hd.nameId == bc.nameId) = false from Bool.eq_false_iff.mpr h]
        exact ih htl (fun c hc => huniq c (List.mem_cons.mpr (Or.inr hc)))

/-- The transform function that `bundleToEnv` applies to each `BundleConst`. -/
private def mkConstDecl (c : BundleConst) : SConstDecl :=
  match c.valueExpr? with
  | some val =>
      { name := c.nameId
        type := fun us => instantiateWithLevels c.levelParamIds us c.typeExpr
        value? := some (fun us => instantiateWithLevels c.levelParamIds us val) }
  | none =>
      { name := c.nameId
        type := fun us => instantiateWithLevels c.levelParamIds us c.typeExpr
        value? := none }

private theorem mkConstDecl_name (c : BundleConst) : (mkConstDecl c).name = c.nameId := by
  unfold mkConstDecl; split <;> rfl

private theorem mkConstDecl_type_identity (c : BundleConst) :
    (mkConstDecl c).type (c.levelParamIds.map ULevel.param) = c.typeExpr := by
  unfold mkConstDecl; split <;> exact instantiateWithLevels_identity c.levelParamIds c.typeExpr

private theorem bundleToEnv_consts (b : ArbitraryLeanKernelBundle) :
    (bundleToEnv b).consts = b.envConsts.map mkConstDecl := by
  unfold bundleToEnv mkConstDecl; rfl

private theorem bundleToEnv_beqName (b : ArbitraryLeanKernelBundle) :
    (bundleToEnv b).beqName = (· == ·) := by
  unfold bundleToEnv; rfl

/-- **`bundleToEnv` preserves types** at identity universe substitution,
given unique nameIds. -/
theorem envPreservesTypes_of_unique_names
    (b : ArbitraryLeanKernelBundle)
    (huniq : ∀ c1 ∈ b.envConsts, ∀ c2 ∈ b.envConsts,
      c1.nameId = c2.nameId → c1 = c2) :
    EnvPreservesTypes b := by
  intro bc hbc
  show (bundleToEnv b).constType? bc.nameId (bc.levelParamIds.map ULevel.param) = some bc.typeExpr
  unfold Environment.Env.constType? Environment.Env.constDecl?
  rw [bundleToEnv_beqName, bundleToEnv_consts]
  rw [find_mapped_envConst b.envConsts bc hbc
    (fun c hc heq => huniq c hc bc hbc heq) mkConstDecl mkConstDecl_name]
  simp only [Option.map]
  exact congrArg some (mkConstDecl_type_identity bc)

/-- **`bundleToEnv` preserves values** at identity universe substitution,
given unique nameIds. -/
theorem envPreservesValues_of_unique_names
    (b : ArbitraryLeanKernelBundle)
    (huniq : ∀ c1 ∈ b.envConsts, ∀ c2 ∈ b.envConsts,
      c1.nameId = c2.nameId → c1 = c2) :
    EnvPreservesValues b := by
  intro bc hbc val hval
  show (bundleToEnv b).constValue? bc.nameId (bc.levelParamIds.map ULevel.param) = some val
  unfold Environment.Env.constValue? Environment.Env.constDecl?
  rw [bundleToEnv_beqName, bundleToEnv_consts]
  rw [find_mapped_envConst b.envConsts bc hbc
    (fun c hc heq => huniq c hc bc hbc heq) mkConstDecl mkConstDecl_name]
  unfold mkConstDecl
  cases hv : bc.valueExpr? with
  | none => simp [hv] at hval
  | some v =>
    simp only [Option.map]
    have : val = v := by
      have h : some v = some val := by rw [← hv]; exact hval
      exact (Option.some.inj h).symm
    rw [this]
    exact congrArg some (instantiateWithLevels_identity bc.levelParamIds v)

end BundleFaithfulness

end LeanKernel
end LoF
end HeytingLean
