import HeytingLean.Core.WitnessChain

namespace HeytingLean.Tests.Core

open HeytingLean.Core

structure SimplifyWitness where
  input : String
  simplified : String
  law : simplified.length <= input.length

instance : IsChainRoot SimplifyWitness where
  rootEvidence w := w.simplified.length <= w.input.length

structure NormalizeWitness where
  sourceSimplify : SimplifyWitness
  normalized : String
  law : normalized = sourceSimplify.simplified

instance : IsWitnessStep NormalizeWitness where
  Upstream := SimplifyWitness
  upstream w := w.sourceSimplify

structure VerifyWitness where
  sourceNormalize : NormalizeWitness
  verified : Bool
  law : verified = true

instance : IsWitnessStep VerifyWitness where
  Upstream := NormalizeWitness
  upstream w := w.sourceNormalize

local instance : IsWitnessStep (IsWitnessStep.Upstream (W := VerifyWitness)) where
  Upstream := SimplifyWitness
  upstream w := w.sourceSimplify

def mkSimplifyWitness (input : String) : SimplifyWitness :=
  { input := input
    simplified := input
    law := Nat.le_refl _ }

def mkNormalizeWitness (w1 : SimplifyWitness) : NormalizeWitness :=
  { sourceSimplify := w1
    normalized := w1.simplified
    law := rfl }

def mkVerifyWitness (w2 : NormalizeWitness) : VerifyWitness :=
  { sourceNormalize := w2
    verified := true
    law := rfl }

theorem step1 (input : String) : Nonempty SimplifyWitness :=
  ⟨mkSimplifyWitness input⟩

theorem step2 (w1 : SimplifyWitness) : Nonempty NormalizeWitness :=
  ⟨mkNormalizeWitness w1⟩

theorem step3 (w2 : NormalizeWitness) : Nonempty VerifyWitness :=
  ⟨mkVerifyWitness w2⟩

theorem simplify_normalize_verify_chain (input : String) :
    exists w3 : VerifyWitness, w3.verified = true /\
      w3.sourceNormalize.sourceSimplify.input = input := by
  let w1 : SimplifyWitness := mkSimplifyWitness input
  let w2 : NormalizeWitness := mkNormalizeWitness w1
  let w3 : VerifyWitness := mkVerifyWitness w2
  refine Exists.intro w3 ?_
  refine And.intro w3.law ?_
  rfl

theorem verify_step_has_upstream (input : String) :
    exists w2 : NormalizeWitness, IsWitnessStep.upstream (mkVerifyWitness (mkNormalizeWitness (mkSimplifyWitness input))) = w2 := by
  exact upstream_exists (W := VerifyWitness) _

theorem verify_step_has_root (input : String) :
    exists w1 : IsWitnessStep.Upstream (W := NormalizeWitness),
      upstream2 (W := VerifyWitness) (mkVerifyWitness (mkNormalizeWitness (mkSimplifyWitness input))) = w1 := by
  exact upstream2_exists (W := VerifyWitness) _

end HeytingLean.Tests.Core
