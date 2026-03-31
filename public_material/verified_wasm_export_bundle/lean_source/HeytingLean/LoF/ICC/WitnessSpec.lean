import HeytingLean.LoF.ICC.GPUVerifierTranslate

namespace HeytingLean
namespace LoF
namespace ICC

inductive WitnessRuleType where
  | beta
  | appBridge
  | annLam
  | annBridge
  | legacyY
  | appLeft
  | appRight
  | annLeft
  | annRight
  deriving DecidableEq, Repr

structure WitnessEntry where
  ruleType : WitnessRuleType
  leftAgent : UInt32
  rightAgent : UInt32
  deriving DecidableEq, Repr

def witnessRuleTypeCode : WitnessRuleType → Nat
  | .beta => 0
  | .appBridge => 1
  | .annLam => 2
  | .annBridge => 3
  | .legacyY => 4
  | .appLeft => 5
  | .appRight => 6
  | .annLeft => 7
  | .annRight => 8

def witnessEntryCells (entry : WitnessEntry) : List Int :=
  [ Int.ofNat (witnessRuleTypeCode entry.ruleType)
  , Int.ofNat entry.leftAgent.toNat
  , Int.ofNat entry.rightAgent.toNat
  ]

def flattenWitnessEntries : List WitnessEntry → List Int
  | [] => []
  | entry :: rest => witnessEntryCells entry ++ flattenWitnessEntries rest

theorem witnessRuleTypeCode_injective {x y : WitnessRuleType}
    (h : witnessRuleTypeCode x = witnessRuleTypeCode y) : x = y := by
  cases x <;> cases y <;> simp [witnessRuleTypeCode] at h <;> rfl

def termAgentTag : Term → UInt32
  | .var _ => 0
  | .lam _ => 1
  | .app _ _ => 2
  | .bridge _ => 3
  | .ann _ _ => 4

def slotLeftAgent : UInt32 := 4097
def slotRightAgent : UInt32 := 4098

def stepEvent? : Term → Option (WitnessEntry × Term)
  | .app (.bridge (.ann (.var 0) (.var 0))) arg =>
      some
        ( { ruleType := .legacyY
            leftAgent := termAgentTag legacyY
            rightAgent := termAgentTag arg }
        , .app arg (.app legacyY arg))
  | .app (.lam body) arg =>
      some
        ( { ruleType := .beta
            leftAgent := termAgentTag (.lam body)
            rightAgent := termAgentTag arg }
        , Term.subst0 arg body)
  | .app (.bridge body) arg =>
      some
        ( { ruleType := .appBridge
            leftAgent := termAgentTag (.bridge body)
            rightAgent := termAgentTag arg }
        , .bridge (.app body (.ann (.var 0) (arg.shift 1))))
  | .ann val (.lam body) =>
      some
        ( { ruleType := .annLam
            leftAgent := termAgentTag val
            rightAgent := termAgentTag (.lam body) }
        , .lam (.ann (.app (val.shift 1) (.var 0)) (Term.subst0 (.bridge (.var 0)) body)))
  | .ann val (.bridge body) =>
      some
        ( { ruleType := .annBridge
            leftAgent := termAgentTag val
            rightAgent := termAgentTag (.bridge body) }
        , Term.subst0 val body)
  | .app fn arg =>
      match stepEvent? fn with
      | some (_, fn') =>
          some
            ( { ruleType := .appLeft
                leftAgent := termAgentTag (.app fn arg)
                rightAgent := slotLeftAgent }
            , .app fn' arg)
      | none =>
          match stepEvent? arg with
          | some (_, arg') =>
              some
                ( { ruleType := .appRight
                    leftAgent := termAgentTag (.app fn arg)
                    rightAgent := slotRightAgent }
                , .app fn arg')
          | none => none
  | .ann val typ =>
      match stepEvent? val with
      | some (_, val') =>
          some
            ( { ruleType := .annLeft
                leftAgent := termAgentTag (.ann val typ)
                rightAgent := slotLeftAgent }
            , .ann val' typ)
      | none =>
          match stepEvent? typ with
          | some (_, typ') =>
              some
                ( { ruleType := .annRight
                    leftAgent := termAgentTag (.ann val typ)
                    rightAgent := slotRightAgent }
                , .ann val typ')
          | none => none
  | _ => none

def inferReplayFuel : Nat → Term → Option (List WitnessEntry × Term)
  | 0, t =>
      if stepEvent? t = none then
        some ([], t)
      else
        none
  | fuel + 1, t =>
      match stepEvent? t with
      | none => some ([], t)
      | some (entry, u) =>
          match inferReplayFuel fuel u with
          | some (rest, out) => some (entry :: rest, out)
          | none => none

def replayEntries : Term → List WitnessEntry → Option Term
  | t, [] =>
      match stepEvent? t with
      | none => some t
      | some _ => none
  | t, entry :: rest =>
      match stepEvent? t with
      | some (expected, u) =>
          if entry = expected then
            replayEntries u rest
          else
            none
      | none => none

theorem replayEntries_of_inferReplayFuel {fuel : Nat} {t : Term}
    {entries : List WitnessEntry} {out : Term}
    (hInfer : inferReplayFuel fuel t = some (entries, out)) :
    replayEntries t entries = some out := by
  induction fuel generalizing t entries out with
  | zero =>
      by_cases hStep : stepEvent? t = none
      · simp [inferReplayFuel, hStep] at hInfer
        cases hInfer
        subst entries
        subst out
        simp [replayEntries, hStep]
      · simp [inferReplayFuel, hStep] at hInfer
  | succ fuel ih =>
      cases hStep : stepEvent? t with
      | none =>
          simp [inferReplayFuel, hStep] at hInfer
          cases hInfer
          subst entries
          subst out
          simp [replayEntries, hStep]
      | some pair =>
          cases pair with
          | mk firstEntry u =>
              cases hRest : inferReplayFuel fuel u with
              | none =>
                  simp [inferReplayFuel, hStep, hRest] at hInfer
              | some restPair =>
                  cases restPair with
                  | mk rest out' =>
                      simp [inferReplayFuel, hStep, hRest] at hInfer
                      cases hInfer
                      subst entries
                      subst out
                      simp [replayEntries, hStep]
                      exact ih hRest

theorem witnessEntryCells_injective {x y : WitnessEntry}
    (h : witnessEntryCells x = witnessEntryCells y) : x = y := by
  cases x with
  | mk ruleX leftX rightX =>
      cases y with
      | mk ruleY leftY rightY =>
          simp [witnessEntryCells, witnessRuleTypeCode] at h
          rcases h with ⟨hRule, hLeft, hRight⟩
          have hRuleNat : witnessRuleTypeCode ruleX = witnessRuleTypeCode ruleY := Int.ofNat_inj.mp hRule
          have hLeftNat : leftX.toNat = leftY.toNat := Int.ofNat_inj.mp hLeft
          have hRightNat : rightX.toNat = rightY.toNat := Int.ofNat_inj.mp hRight
          have hRule' : ruleX = ruleY := witnessRuleTypeCode_injective hRuleNat
          have hLeft' : leftX = leftY := UInt32.toNat_inj.mp hLeftNat
          have hRight' : rightX = rightY := UInt32.toNat_inj.mp hRightNat
          subst hRule'
          subst hLeft'
          subst hRight'
          rfl

theorem flattenWitnessEntries_injective {xs ys : List WitnessEntry}
    (h : flattenWitnessEntries xs = flattenWitnessEntries ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          simp [flattenWitnessEntries, witnessEntryCells] at h
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp [flattenWitnessEntries, witnessEntryCells] at h
      | cons y ys =>
          have hHead : witnessEntryCells x = witnessEntryCells y := by
            have := congrArg (List.take 3) h
            simpa [flattenWitnessEntries, witnessEntryCells] using this
          have hTail : flattenWitnessEntries xs = flattenWitnessEntries ys := by
            have := congrArg (List.drop 3) h
            simpa [flattenWitnessEntries, witnessEntryCells] using this
          have hxy : x = y := witnessEntryCells_injective hHead
          have hrest : xs = ys := ih hTail
          subst hxy
          subst hrest
          rfl

theorem flattenWitnessEntries_length (xs : List WitnessEntry) :
    (flattenWitnessEntries xs).length = 3 * xs.length := by
  induction xs with
  | nil =>
      simp [flattenWitnessEntries]
  | cons x xs ih =>
      simp [flattenWitnessEntries, witnessEntryCells, ih, Nat.mul_succ, Nat.add_assoc]

theorem replayEntries_deterministic {t : Term} {xs ys : List WitnessEntry}
    {outX outY : Term}
    (hx : replayEntries t xs = some outX)
    (hy : replayEntries t ys = some outY) :
    xs = ys ∧ outX = outY := by
  induction xs generalizing t ys outX outY with
  | nil =>
      cases hStep : stepEvent? t with
      | none =>
          simp [replayEntries, hStep] at hx
          subst outX
          cases ys with
          | nil =>
              simp [replayEntries, hStep] at hy
              cases hy
              exact ⟨rfl, rfl⟩
          | cons y ys =>
              simp [replayEntries, hStep] at hy
      | some pair =>
          simp [replayEntries, hStep] at hx
  | cons x xs ih =>
      cases hStep : stepEvent? t with
      | none =>
          simp [replayEntries, hStep] at hx
      | some pair =>
          cases pair with
          | mk expected u =>
              by_cases hxe : x = expected
              · simp [replayEntries, hStep, hxe] at hx
                cases ys with
                | nil =>
                    simp [replayEntries, hStep] at hy
                | cons y ys =>
                    by_cases hye : y = expected
                    · simp [replayEntries, hStep, hye] at hy
                      rcases ih hx hy with ⟨hrest, hout⟩
                      have hxy : x = y := by
                        calc
                          x = expected := hxe
                          _ = y := hye.symm
                      subst hxy
                      subst hrest
                      exact ⟨rfl, hout⟩
                    · simp [replayEntries, hStep, hye] at hy
              · simp [replayEntries, hStep, hxe] at hx

theorem replayEntries_eq_canonical_iff {t out : Term} {canonical witness : List WitnessEntry}
    (hCanonical : replayEntries t canonical = some out) :
    replayEntries t witness = some out ↔ witness = canonical := by
  constructor
  · intro hWitness
    exact (replayEntries_deterministic hWitness hCanonical).1
  · intro hEq
    subst hEq
    exact hCanonical

def verifierAcceptsBool (witness : ICCVerifierWitness) : Bool :=
  decide (step? witness.certificate = some witness.expected) && witness.expected.annFree

def sourceWitnessMeaningBool (src : SourceWitness) : Bool :=
  match actualTarget? src.law src.source with
  | some actualTarget => decide (actualTarget = src.target)
  | none => false

structure ICCCanonicalWitness where
  sourceId : String
  law : WitnessLaw
  source : LoFPrimary.Expr 0
  target : LoFPrimary.Expr 0
  actualTarget : LoFPrimary.Expr 0
  certificate : Term
  normalized : Term
  expected : Term
  provenance : String
  sourceFamily : String
  sourceModuleName? : Option String := none
  sourceDeclName? : Option String := none
  commonSourceId? : Option String := none
  proofGraphModuleName? : Option String := none
  proofGraphDeclName? : Option String := none
  skyModuleName? : Option String := none
  skyDeclName? : Option String := none
  translationTag : String
  tags : List String := []
  expectedAccepted : Bool
  acceptedInLean : Bool
  meaningHolds : Bool
  witness : List WitnessEntry
  deriving Repr

def canonicalWitnessAccepted (row : ICCCanonicalWitness) : Prop :=
  replayEntries row.certificate row.witness = some row.normalized ∧
    step? row.certificate = some row.expected ∧
    row.expected.annFree = true ∧
    row.normalized.annFree = true

def buildCanonicalWitness
    (fuel : Nat) (expectedAccepted : Bool) (src : SourceWitness) (witness : ICCVerifierWitness) :
    Except String ICCCanonicalWitness :=
  match inferReplayFuel fuel witness.certificate with
  | some (trace, normalized) =>
      .ok
        { sourceId := witness.sourceId
          law := witness.law
          source := witness.source
          target := witness.target
          actualTarget := witness.actualTarget
          certificate := witness.certificate
          normalized := normalized
          expected := witness.expected
          provenance := witness.provenance
          sourceFamily := witness.sourceFamily
          sourceModuleName? := witness.sourceModuleName?
          sourceDeclName? := witness.sourceDeclName?
          commonSourceId? := witness.commonSourceId?
          proofGraphModuleName? := witness.proofGraphModuleName?
          proofGraphDeclName? := witness.proofGraphDeclName?
          skyModuleName? := witness.skyModuleName?
          skyDeclName? := witness.skyDeclName?
          translationTag := witness.translationTag
          tags := witness.tags
          expectedAccepted := expectedAccepted
          acceptedInLean := verifierAcceptsBool witness
          meaningHolds := sourceWitnessMeaningBool src
          witness := trace }
  | none =>
      .error s!"could not infer replay witness within fuel {fuel} for {witness.sourceId}"

theorem buildCanonicalWitness_replays
    {fuel : Nat} {expectedAccepted : Bool} {src : SourceWitness} {w : ICCVerifierWitness}
    {row : ICCCanonicalWitness}
    (hBuild : buildCanonicalWitness fuel expectedAccepted src w = Except.ok row) :
    replayEntries row.certificate row.witness = some row.normalized := by
  unfold buildCanonicalWitness at hBuild
  cases hInfer : inferReplayFuel fuel w.certificate with
  | none =>
      simp [hInfer] at hBuild
  | some payload =>
      cases payload with
      | mk trace normalized =>
          simp [hInfer] at hBuild
          cases hBuild
          exact replayEntries_of_inferReplayFuel hInfer

end ICC
end LoF
end HeytingLean
