import HeytingLean.HeytingVeil.Temporal.Core
import HeytingLean.HeytingVeil.Verify.Core

namespace HeytingLean
namespace HeytingVeil
namespace Refinement

open HeytingLean.HeytingVeil.Temporal
open HeytingLean.HeytingVeil.Verify

universe u v

variable {SrcState : Type u} {TgtState : Type v}

structure StutteringSimulation (Msrc : Machine SrcState) (Mtgt : Machine TgtState)
    (encode : SrcState → TgtState) : Prop where
  init_preserved : ∀ s, Msrc.Init s → Mtgt.Init (encode s)
  step_or_stutter : ∀ s t, Msrc.Step s t →
    Mtgt.Step (encode s) (encode t) ∨ encode s = encode t

def pullbackInv (encode : SrcState → TgtState) (Inv : TgtState → Prop) : SrcState → Prop :=
  fun s => Inv (encode s)

def pullbackInvariantCert
    {Msrc : Machine SrcState} {Mtgt : Machine TgtState}
    {encode : SrcState → TgtState} {Inv : TgtState → Prop}
    (sim : StutteringSimulation Msrc Mtgt encode)
    (cert : InvariantCert Mtgt Inv) :
    InvariantCert Msrc (pullbackInv encode Inv) where
  init_holds := by
    intro s hs
    exact cert.init_holds (encode s) (sim.init_preserved s hs)
  step_preserves := by
    intro s t hs hst
    rcases sim.step_or_stutter s t hst with hstep | hstutter
    · exact cert.step_preserves (encode s) (encode t) hs hstep
    · simpa [pullbackInv, hstutter] using hs

theorem stuttering_simulation_preserves_safety
    {Msrc : Machine SrcState} {Mtgt : Machine TgtState}
    {encode : SrcState → TgtState} {Inv : TgtState → Prop}
    (sim : StutteringSimulation Msrc Mtgt encode)
    (cert : InvariantCert Mtgt Inv)
    {σ : Trace SrcState} (hσ : ValidTrace Msrc σ) :
    Safety (pullbackInv encode Inv) σ := by
  exact safety_of_certificate (cert := pullbackInvariantCert sim cert) hσ

theorem stuttering_simulation_preserves_liveness
    {Msrc : Machine SrcState} {_Mtgt : Machine TgtState}
    {encode : SrcState → TgtState}
    (P : TgtState → Prop)
    (hL :
      ∀ σ : Trace SrcState, ValidTrace Msrc σ → Eventually (fun n => P (encode (σ n))))
    {σ : Trace SrcState} (hσ : ValidTrace Msrc σ) :
    Eventually (fun n => P (encode (σ n))) := by
  exact hL σ hσ

end Refinement
end HeytingVeil
end HeytingLean
