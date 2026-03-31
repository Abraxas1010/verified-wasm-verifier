import HeytingLean.Categorical.KoopmanAlgebra
import HeytingLean.CDL.TrainingStep

/-!
# Categorical training-step instantiations

This module instantiates `CDL.TrainingStep` for Koopman-style architectures,
bridging categorical architecture definitions to a typed optimization-step surface.
-/

namespace HeytingLean
namespace Categorical

open CDL
open CDL.Para

universe u

namespace KoopmanNBA

variable {X S O : Type u}
variable [SemilatticeInf S] [OrderBot S]

/-- Parametric forward map for a Koopman architecture with untied encoder/decoder parameters. -/
def forwardPara (K : KoopmanNBA X S O) : ParaHom X O :=
  ⟨K.encoder.P × K.decoder.P, fun
    | ((pEnc, pDec), x) => K.forward pEnc pDec x⟩

@[simp] theorem forwardPara_P (K : KoopmanNBA X S O) :
    (forwardPara K).P = (K.encoder.P × K.decoder.P) := rfl

/-- One-step training semantics for Koopman architectures with separate encoder/decoder updates. -/
def trainingStep (K : KoopmanNBA X S O)
    (updateEnc : K.encoder.P × X × O → K.encoder.P)
    (updateDec : K.decoder.P × S × O → K.decoder.P) :
    CDL.TrainingStep X O where
  model := forwardPara K
  update := fun
    | ((pEnc, pDec), x, o) =>
        let s := K.latent pEnc x
        (updateEnc (pEnc, x, o), updateDec (pDec, s, o))

@[simp] theorem trainingStep_model_P (K : KoopmanNBA X S O)
    (updateEnc : K.encoder.P × X × O → K.encoder.P)
    (updateDec : K.decoder.P × S × O → K.decoder.P) :
    (trainingStep K updateEnc updateDec).model.P = (K.encoder.P × K.decoder.P) := rfl

@[simp] theorem trainingStep_step (K : KoopmanNBA X S O)
    (updateEnc : K.encoder.P × X × O → K.encoder.P)
    (updateDec : K.decoder.P × S × O → K.decoder.P)
    (pEnc : K.encoder.P) (pDec : K.decoder.P) (x : X) :
    CDL.TrainingStep.step (trainingStep K updateEnc updateDec) (pEnc, pDec) x =
      ((updateEnc (pEnc, x, K.forward pEnc pDec x),
        updateDec (pDec, K.latent pEnc x, K.forward pEnc pDec x)),
       K.forward pEnc pDec x) := rfl

end KoopmanNBA

namespace TiedKoopmanNBA

variable {X S O P : Type u}
variable [SemilatticeInf S] [OrderBot S]

/-- Parametric forward map for tied-parameter Koopman architectures. -/
def forwardPara (K : TiedKoopmanNBA X S O P) : ParaHom X O :=
  ⟨P, fun
    | (p, x) => K.forward p x⟩

@[simp] theorem forwardPara_P (K : TiedKoopmanNBA X S O P) :
    (forwardPara K).P = P := rfl

/-- One-step training semantics for tied-parameter Koopman architectures. -/
def trainingStep (K : TiedKoopmanNBA X S O P) (update : P × X × O → P) :
    CDL.TrainingStep X O where
  model := forwardPara K
  update := update

@[simp] theorem trainingStep_model_P (K : TiedKoopmanNBA X S O P) (update : P × X × O → P) :
    (trainingStep K update).model.P = P := rfl

@[simp] theorem trainingStep_step (K : TiedKoopmanNBA X S O P)
    (update : P × X × O → P) (p : P) (x : X) :
    CDL.TrainingStep.step (trainingStep K update) p x =
      (update (p, x, K.forward p x), K.forward p x) := rfl

end TiedKoopmanNBA

end Categorical
end HeytingLean
