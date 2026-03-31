import HeytingLean.CDL
import HeytingLean.Categorical.TrainingStep

/-!
# Tests: CDL sanity

Small compile-time regression tests for the `HeytingLean.CDL` (Categorical Deep Learning) spine:

- parameter stacking in `Para(Type)`,
- comonoid laws imply diagonal comultiplication in cartesian `Type`,
- orbit-based tying respects `R`-equivalence,
- the 2-step folding RNN example produces an explicit tying witness.
-/

namespace HeytingLean.Tests.CDL

open HeytingLean.CDL
open HeytingLean.CDL.Para

universe u

namespace Para

variable {X Y Z : Type u} (f : ParaHom X Y) (g : ParaHom Y Z)

theorem comp_param_stacks : (ParaHom.comp g f).P = (g.P × f.P) := rfl

end Para

namespace Comonoid

open HeytingLean.CDL

variable {P : Type u} (C : ComonoidStruct P)

theorem comult_is_diag : C.comult = fun p => (p, p) :=
  ComonoidStruct.comult_eq_diag (C := C)

end Comonoid

namespace Orbit

open HeytingLean.CDL.Orbit

theorem embed_respects (t u : Nat) (h : REq (fun n => n % 2) t u) :
    embed (ProofTerm := Nat) (R := fun n => n % 2) (Param := Nat) (fun _ => 0) t =
      embed (ProofTerm := Nat) (R := fun n => n % 2) (Param := Nat) (fun _ => 0) u := by
  simpa using
    (embed_respects_R (ProofTerm := Nat) (R := fun n => n % 2) (Param := Nat) (W := fun _ => 0) (t := t)
      (u := u) h)

end Orbit

namespace FoldingRNN

open HeytingLean.CDL.Examples
open HeytingLean.CDL.Examples.FoldingRNN

theorem unroll2_has_tying_witness {A S : Type u} (cell : Examples.Cell A S) :
    Nonempty
      (Para2Hom (FoldingRNN.unroll2_sep (cell := cell)) (FoldingRNN.unroll2_tied (cell := cell))) :=
  ⟨FoldingRNN.unroll2_ties (cell := cell)⟩

end FoldingRNN

namespace ParaMealy

open HeytingLean.CDL.Coalgebra

variable {I M O S₁ S₂ : Type u}

theorem seq_param_stacks (m1 : Coalgebra.ParaMealy I M S₁) (m2 : Coalgebra.ParaMealy M O S₂) :
    (Coalgebra.ParaMealy.seq m1 m2).P = (m1.P × m2.P) := rfl

end ParaMealy

namespace TrainingStep

open HeytingLean.CDL

variable {X Y Z : Type u} (f : CDL.TrainingStep X Y) (g : CDL.TrainingStep Y Z)

theorem comp_param_stacks :
    (CDL.TrainingStep.comp g f).model.P = (g.model.P × f.model.P) := rfl

theorem id_step_is_noop (x : X) :
    CDL.TrainingStep.step (CDL.TrainingStep.id X) PUnit.unit x = (PUnit.unit, x) := rfl

end TrainingStep

namespace TrainingStepInvariant

open HeytingLean.CDL

/-- Constrained executable training step: keep parameter fixed, emit `p + x`. -/
def frozenNatStep : CDL.TrainingStep Nat Nat where
  model := ⟨Nat, fun
    | (p, x) => p + x⟩
  update := fun
    | (p, _, _) => p

def anchored (p0 : Nat) : Nat → Prop := fun p => p = p0

theorem frozenNatStep_exec (p x : Nat) :
    CDL.TrainingStep.step frozenNatStep p x = (p, p + x) := rfl

theorem frozenNatStep_preserves_anchor (p0 x : Nat) :
    anchored p0 ((CDL.TrainingStep.step frozenNatStep p0 x).1) := by
  have hupdate :
      ∀ p x, anchored p0 p →
        anchored p0 (frozenNatStep.update (p, x, CDL.TrainingStep.output frozenNatStep p x)) := by
    intro p x hp
    simpa [anchored, frozenNatStep] using hp
  exact CDL.TrainingStep.step_preserves (t := frozenNatStep) (Inv := anchored p0) hupdate (p := p0) rfl x

end TrainingStepInvariant

namespace KoopmanTrainingStep

open HeytingLean.Categorical

variable {X S O : Type u}
variable [SemilatticeInf S] [OrderBot S]
variable (K : KoopmanNBA X S O)
variable (updateEnc : K.encoder.P × X × O → K.encoder.P)
variable (updateDec : K.decoder.P × S × O → K.decoder.P)

theorem model_param_pair :
    (KoopmanNBA.trainingStep K updateEnc updateDec).model.P = (K.encoder.P × K.decoder.P) := rfl

end KoopmanTrainingStep

namespace ArchitectureGraph

open HeytingLean.CDL
open HeytingLean.CDL.Para
open HeytingLean.CategoryTheory.Polynomial

def inputToLatent : Para.TypedNode Nat Nat where
  model := ParaHom.id Nat
  inPort := ArchPortKind.input
  outPort := ArchPortKind.latent

def latentToOutput : Para.TypedNode Nat Nat where
  model := ParaHom.id Nat
  inPort := ArchPortKind.latent
  outPort := ArchPortKind.output

def outputToLoss : Para.TypedNode Nat Nat where
  model := ParaHom.id Nat
  inPort := ArchPortKind.output
  outPort := ArchPortKind.loss

def badOutputNode : Para.TypedNode Nat Nat where
  model := ParaHom.id Nat
  inPort := ArchPortKind.output
  outPort := ArchPortKind.output

theorem compose_accepts_compatible :
    (Para.composeIfCompatible? inputToLatent latentToOutput).isSome = true := by
  simp [inputToLatent, latentToOutput, Para.composeIfCompatible?]

theorem compose_rejects_mismatch :
    Para.composeIfCompatible? inputToLatent badOutputNode = none := by
  simp [inputToLatent, badOutputNode, Para.composeIfCompatible?]

def validTwoEdgeCandidate : ArchCandidate :=
  { nodes := #[
      TypedNode.toArchNode inputToLatent,
      TypedNode.toArchNode latentToOutput,
      TypedNode.toArchNode outputToLoss
    ]
    edges := #[
      { src := 0, dst := 1 },
      { src := 1, dst := 2 }
    ] }

def invalidMismatchCandidate : ArchCandidate :=
  { nodes := #[
      TypedNode.toArchNode inputToLatent,
      TypedNode.toArchNode badOutputNode
    ]
    edges := #[
      { src := 0, dst := 1 }
    ] }

theorem valid_candidate_accepts :
    validCandidate validTwoEdgeCandidate = true := by
  native_decide

theorem invalid_candidate_rejected :
    validCandidate invalidMismatchCandidate = false := by
  native_decide

end ArchitectureGraph

end HeytingLean.Tests.CDL
