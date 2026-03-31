import HeytingLean.LoF.ICC.GPUVerifierContract

namespace HeytingLean
namespace LoF
namespace ICC

def buildWitness (src : SourceWitness) (actualTarget : LoFPrimary.Expr 0) :
    ICCVerifierWitness :=
  let actualPayload := encodePrimaryFixture actualTarget
  let expectedPayload := encodePrimaryFixture src.target
  let certificate :=
    match src.law with
    | .calling => callingCertificate actualPayload
    | .crossing => crossingCertificate actualPayload
  { sourceId := src.sourceId
    law := src.law
    source := src.source
    target := src.target
    actualTarget := actualTarget
    certificate := certificate
    expected := expectedPayload
    provenance := src.provenance
    sourceFamily := src.sourceFamily
    sourceModuleName? := src.sourceModuleName?
    sourceDeclName? := src.sourceDeclName?
    commonSourceId? := src.commonSourceId?
    proofGraphModuleName? := src.proofGraphModuleName?
    proofGraphDeclName? := src.proofGraphDeclName?
    skyModuleName? := src.skyModuleName?
    skyDeclName? := src.skyDeclName?
    translationTag :=
      match src.law with
      | .calling => "icc_gpu_verifier_calling_v1"
      | .crossing => "icc_gpu_verifier_crossing_v1"
    tags := src.tags }

def translateVerifierWitness (src : SourceWitness) : Except String ICCVerifierWitness :=
  match actualTarget? src.law src.source with
  | some actualTarget => .ok (buildWitness src actualTarget)
  | none =>
      .error s!"unsupported source witness for law {repr src.law}: {repr src.source}"

theorem buildWitness_accepts_of_target_eq (src : SourceWitness) (actualTarget : LoFPrimary.Expr 0)
    (hTarget : src.target = actualTarget) :
    ICCVerifierAccepts (buildWitness src actualTarget) := by
  rcases src with
    ⟨sourceId, law, source, target, provenance, sourceFamily, sourceModuleName?,
      sourceDeclName?, commonSourceId?, proofGraphModuleName?, proofGraphDeclName?,
      skyModuleName?, skyDeclName?, tags⟩
  subst actualTarget
  cases law <;>
    simp [ICCVerifierAccepts, buildWitness, encodePrimaryFixture_annFree,
      callingCertificate_step, crossingCertificate_step, subst0_var0]

theorem translateVerifierWitness_accepts_of_meaning {src : SourceWitness} {w : ICCVerifierWitness}
    (hTranslate : translateVerifierWitness src = Except.ok w)
    (hMeaning : SourceWitnessMeaning src) :
    ICCVerifierAccepts w := by
  rcases src with
    ⟨sourceId, law, source, target, provenance, sourceFamily, sourceModuleName?,
      sourceDeclName?, commonSourceId?, proofGraphModuleName?, proofGraphDeclName?,
      skyModuleName?, skyDeclName?, tags⟩
  unfold SourceWitnessMeaning at hMeaning
  unfold translateVerifierWitness at hTranslate
  rw [hMeaning] at hTranslate
  cases hTranslate
  exact buildWitness_accepts_of_target_eq
    ⟨sourceId, law, source, target, provenance, sourceFamily, sourceModuleName?,
      sourceDeclName?, commonSourceId?, proofGraphModuleName?, proofGraphDeclName?,
      skyModuleName?, skyDeclName?, tags⟩ target rfl

theorem translateVerifierWitness_meaning_of_accepts {src : SourceWitness} {w : ICCVerifierWitness}
    (hTranslate : translateVerifierWitness src = Except.ok w)
    (hAccepts : ICCVerifierAccepts w) :
    VerifierMeaning src := by
  rcases src with
    ⟨sourceId, law, source, target, provenance, sourceFamily, sourceModuleName?,
      sourceDeclName?, commonSourceId?, proofGraphModuleName?, proofGraphDeclName?,
      skyModuleName?, skyDeclName?, tags⟩
  rcases hAccepts with ⟨hStep, _⟩
  unfold VerifierMeaning SourceWitnessMeaning
  unfold translateVerifierWitness at hTranslate
  cases hActual : actualTarget? law source with
  | none =>
      simp [hActual] at hTranslate
  | some actualTarget =>
      simp [hActual] at hTranslate
      cases hTranslate
      cases law <;>
        simp [buildWitness, callingCertificate_step, crossingCertificate_step, subst0_var0] at hStep
      case calling =>
        have hEq : target = actualTarget :=
          encodePrimaryFixture_injective hStep.symm
        simp [hEq]
      case crossing =>
        have hEq : target = actualTarget :=
          encodePrimaryFixture_injective hStep.symm
        simp [hEq]

theorem translateVerifierWitness_accepts_iff_meaning {src : SourceWitness} {w : ICCVerifierWitness}
    (hTranslate : translateVerifierWitness src = Except.ok w) :
    ICCVerifierAccepts w ↔ VerifierMeaning src := by
  constructor
  · exact translateVerifierWitness_meaning_of_accepts hTranslate
  · exact translateVerifierWitness_accepts_of_meaning hTranslate

end ICC
end LoF
end HeytingLean
