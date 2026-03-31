import HeytingLean.LoF.ICC.Reduction
import HeytingLean.LoF.ICC.Encodings
import HeytingLean.LoF.LoFPrimary.Rewrite

namespace HeytingLean
namespace LoF
namespace ICC

open HeytingLean.LoF.LoFPrimary

inductive WitnessLaw where
  | calling
  | crossing
  deriving DecidableEq, Repr

structure SourceWitness where
  sourceId : String
  law : WitnessLaw
  source : LoFPrimary.Expr 0
  target : LoFPrimary.Expr 0
  provenance : String
  sourceFamily : String := "compat_seed"
  sourceModuleName? : Option String := none
  sourceDeclName? : Option String := none
  commonSourceId? : Option String := none
  proofGraphModuleName? : Option String := none
  proofGraphDeclName? : Option String := none
  skyModuleName? : Option String := none
  skyDeclName? : Option String := none
  tags : List String := []
  deriving Repr

structure VerifierCorpusSeed where
  sourceId : String
  law : WitnessLaw
  source : LoFPrimary.Expr 0
  target : LoFPrimary.Expr 0
  provenance : String
  sourceFamily : String
  sourceModuleName : String
  sourceDeclName : String
  skyModuleName : String
  skyDeclName : String
  tags : List String := []
  deriving Repr

def mkCommonSourceId (moduleName declName : String) : String :=
  s!"{moduleName}::{declName}"

def VerifierCorpusSeed.toSourceWitness (seed : VerifierCorpusSeed) : SourceWitness :=
  { sourceId := seed.sourceId
    law := seed.law
    source := seed.source
    target := seed.target
    provenance := seed.provenance
    sourceFamily := seed.sourceFamily
    sourceModuleName? := some seed.sourceModuleName
    sourceDeclName? := some seed.sourceDeclName
    commonSourceId? := some (mkCommonSourceId seed.sourceModuleName seed.sourceDeclName)
    proofGraphModuleName? := some seed.sourceModuleName
    proofGraphDeclName? := some seed.sourceDeclName
    skyModuleName? := some seed.skyModuleName
    skyDeclName? := some seed.skyDeclName
    tags := seed.tags }

def actualTarget? : WitnessLaw → LoFPrimary.Expr 0 → Option (LoFPrimary.Expr 0)
  | .calling, .juxt lhs rhs =>
      if lhs = rhs then
        some lhs
      else
        none
  | .crossing, .mark (.mark body) => some body
  | _, _ => none

def SourceWitnessMeaning (src : SourceWitness) : Prop :=
  actualTarget? src.law src.source = some src.target

def VerifierMeaning : SourceWitness → Prop :=
  SourceWitnessMeaning

theorem sourceWitnessMeaning_step (src : SourceWitness) :
    SourceWitnessMeaning src → LoFPrimary.Step src.source src.target := by
  intro h
  rcases src with
    ⟨sourceId, law, source, target, provenance, sourceFamily, sourceModuleName?,
      sourceDeclName?, commonSourceId?, proofGraphModuleName?, proofGraphDeclName?,
      skyModuleName?, skyDeclName?, tags⟩
  cases law <;> cases source <;> simp [SourceWitnessMeaning, actualTarget?] at h
  case calling.juxt lhs rhs =>
    by_cases hEq : lhs = rhs
    · simp [hEq] at h
      have hStep : LoFPrimary.Step (LoFPrimary.Expr.juxt lhs lhs) lhs :=
        LoFPrimary.Step.calling lhs
      subst rhs
      cases h
      exact hStep
    · simp [hEq] at h
  case crossing.mark body =>
    cases body <;> simp at h
    case mark inner =>
      have hStep : LoFPrimary.Step (LoFPrimary.Expr.mark (LoFPrimary.Expr.mark inner)) inner :=
        LoFPrimary.Step.crossing inner
      cases h
      exact hStep

/--
Compatibility encoding used by the current ICC verifier lane.

This is still not a full proof compiler. It is the concrete payload encoding
shared by the Lean contract and the native HVM parity surface.
-/
def encodePrimaryFixture : LoFPrimary.Expr 0 → Term
  | .void => kTerm
  | .var idx => nomatch idx
  | .mark body => .bridge (encodePrimaryFixture body)
  | .juxt lhs rhs =>
      .app (.app sTerm (encodePrimaryFixture lhs)) (encodePrimaryFixture rhs)

@[simp] theorem sTerm_containsAnn : sTerm.containsAnn = false := by
  native_decide

@[simp] theorem encodePrimaryFixture_containsAnn (expr : LoFPrimary.Expr 0) :
    (encodePrimaryFixture expr).containsAnn = false := by
  induction expr with
  | void =>
      native_decide
  | var idx =>
      cases idx.2
  | mark body ih =>
      simpa [encodePrimaryFixture, Term.containsAnn] using ih
  | juxt lhs rhs ihL ihR =>
      simp [encodePrimaryFixture, Term.containsAnn, ihL, ihR, sTerm_containsAnn]

@[simp] theorem encodePrimaryFixture_annFree (expr : LoFPrimary.Expr 0) :
    (encodePrimaryFixture expr).annFree = true := by
  simp [Term.annFree, encodePrimaryFixture_containsAnn]

theorem closedAbove_mono_local {k m : Nat} {t : Term}
    (hkm : k ≤ m) (h : Term.closedAbove k t) :
    Term.closedAbove m t := by
  induction t generalizing k m with
  | var idx =>
      exact Nat.lt_of_lt_of_le h hkm
  | lam body ih =>
      simpa [Term.closedAbove] using ih (Nat.succ_le_succ hkm) h
  | app fn arg ihFn ihArg =>
      rcases h with ⟨hFn, hArg⟩
      exact ⟨ihFn hkm hFn, ihArg hkm hArg⟩
  | bridge body ih =>
      simpa [Term.closedAbove] using ih (Nat.succ_le_succ hkm) h
  | ann val typ ihVal ihTyp =>
      rcases h with ⟨hVal, hTyp⟩
      exact ⟨ihVal hkm hVal, ihTyp hkm hTyp⟩

@[simp] theorem encodePrimaryFixture_closed (expr : LoFPrimary.Expr 0) :
    Term.Closed (encodePrimaryFixture expr) := by
  induction expr with
  | void =>
      simp [encodePrimaryFixture, kTerm, Term.Closed, Term.closedAbove]
  | var idx =>
      cases idx.2
  | mark body ih =>
      simpa [encodePrimaryFixture, Term.Closed, Term.closedAbove] using
        (closedAbove_mono_local (k := 0) (m := 1) (t := encodePrimaryFixture body) (by omega) ih)
  | juxt lhs rhs ihL ihR =>
      simp [encodePrimaryFixture, Term.Closed, Term.closedAbove, closed_sTerm, ihL, ihR]

def erasePrimaryFixture? : Term → Option (LoFPrimary.Expr 0)
  | .var _ => none
  | .bridge body =>
      match erasePrimaryFixture? body with
      | some body' => some (.mark body')
      | none =>
          if (.bridge body : Term) = kTerm then
            some .void
          else
            none
  | .app fn arg =>
      match fn with
      | .app head lhs =>
          if head = sTerm then
            match erasePrimaryFixture? lhs, erasePrimaryFixture? arg with
            | some lhs', some rhs' => some (.juxt lhs' rhs')
            | _, _ => none
          else if (.app (.app head lhs) arg : Term) = kTerm then
            some .void
          else
            none
      | _ =>
          if (.app fn arg : Term) = kTerm then
            some .void
          else
            none
  | .lam body =>
      if (.lam body : Term) = kTerm then
        some .void
      else
        none
  | .ann val typ =>
      if (.ann val typ : Term) = kTerm then
        some .void
      else
        none

@[simp] theorem erasePrimaryFixture_encode (expr : LoFPrimary.Expr 0) :
    erasePrimaryFixture? (encodePrimaryFixture expr) = some expr := by
  induction expr with
  | void =>
      native_decide
  | var idx =>
      cases idx.2
  | mark body ih =>
      simp [erasePrimaryFixture?, encodePrimaryFixture, ih]
  | juxt lhs rhs ihL ihR =>
      simp [erasePrimaryFixture?, encodePrimaryFixture, ihL, ihR]

theorem encodePrimaryFixture_injective :
    Function.Injective encodePrimaryFixture := by
  intro lhs rhs h
  have h' := congrArg erasePrimaryFixture? h
  simpa using h'

/-- Calling-style verifier certificate: collapse an explicit identity shell. -/
def callingCertificate (payload : Term) : Term :=
  .app (.lam (.var 0)) payload

/-- Crossing-style verifier certificate: collapse an explicit bridge annotation shell. -/
def crossingCertificate (payload : Term) : Term :=
  .ann payload (.bridge (.var 0))

@[simp] theorem callingCertificate_step (payload : Term) :
    step? (callingCertificate payload) = some (Term.subst0 payload (.var 0)) := by
  simp [callingCertificate, step?]

@[simp] theorem crossingCertificate_step (payload : Term) :
    step? (crossingCertificate payload) = some (Term.subst0 payload (.var 0)) := by
  simp [crossingCertificate, step?]

theorem callingCertificate_steps (payload : Term) :
    Steps (callingCertificate payload) (Term.subst0 payload (.var 0)) := by
  refine .trans (u := Term.subst0 payload (.var 0)) ?_ (.refl _)
  simpa [callingCertificate] using (Step.beta (body := .var 0) (arg := payload))

theorem crossingCertificate_steps (payload : Term) :
    Steps (crossingCertificate payload) (Term.subst0 payload (.var 0)) := by
  refine .trans (u := Term.subst0 payload (.var 0)) ?_ (.refl _)
  simpa [crossingCertificate] using (Step.ann_bridge (val := payload) (body := .var 0))

@[simp] theorem shiftAbove_zero (payload : Term) (cutoff : Nat) :
    payload.shiftAbove cutoff 0 = payload := by
  induction payload generalizing cutoff with
  | var idx =>
      change Term.var (if idx >= cutoff then idx + 0 else idx) = Term.var idx
      congr
      split <;> omega
  | lam body ih =>
      simp [Term.shiftAbove, ih]
  | app fn arg ihFn ihArg =>
      simp [Term.shiftAbove, ihFn, ihArg]
  | bridge body ih =>
      simp [Term.shiftAbove, ih]
  | ann val typ ihVal ihTyp =>
      simp [Term.shiftAbove, ihVal, ihTyp]

@[simp] theorem subst0_var0 (payload : Term) :
    Term.subst0 payload (.var 0) = payload := by
  simp [Term.subst0, Term.substAt, shiftAbove_zero]

structure ICCVerifierWitness where
  sourceId : String
  law : WitnessLaw
  source : LoFPrimary.Expr 0
  target : LoFPrimary.Expr 0
  actualTarget : LoFPrimary.Expr 0
  certificate : Term
  expected : Term
  provenance : String
  sourceFamily : String := "compat_seed"
  sourceModuleName? : Option String := none
  sourceDeclName? : Option String := none
  commonSourceId? : Option String := none
  proofGraphModuleName? : Option String := none
  proofGraphDeclName? : Option String := none
  skyModuleName? : Option String := none
  skyDeclName? : Option String := none
  translationTag : String
  tags : List String := []
  deriving Repr

def ICCVerifierAccepts (witness : ICCVerifierWitness) : Prop :=
  step? witness.certificate = some witness.expected ∧ witness.expected.annFree = true

abbrev TinyLawWitness := ICCVerifierWitness
abbrev accepts := ICCVerifierAccepts

end ICC
end LoF
end HeytingLean
