import HeytingLean.Constructor.CT.TaskExistence
import HeytingLean.Physics.Photoemission.Tasks

/-!
# Photoemission as a `TaskCT` instance (constructor existence)

This module connects the photoemission channel vocabulary to the CT task layer
(`HeytingLean.Constructor.CT.TaskCT`) by:
- introducing an abstract substrate `Stage` encoding the three-step pipeline;
- defining named CT tasks for absorption/transport/emission and their serial
  composition;
- defining a constructor type whose implementations are constrained by simple
  physical side conditions (energy threshold, positivity of parameters).

The goal is *structural*: it makes the three-step model available to the CT
composition lemmas (`possible_seq`, etc.), and provides a clean place to record
“physical constraints ⇒ task impossibility” results.
-/

noncomputable section

namespace HeytingLean
namespace Physics
namespace Photoemission

open HeytingLean.Constructor.CT

/-- Abstract “stage” substrate for the three-step photoemission pipeline. -/
inductive Stage
  | bulkGround
  | bulkExcited
  | surface
  | vacuum
  deriving DecidableEq

namespace Stage

def attr (s : Stage) : Attribute Stage :=
  {x | x = s}

theorem attr_ne {a b : Stage} (h : a ≠ b) : attr a ≠ attr b := by
  intro hab
  have ha : a ∈ attr a := by
    simp [attr]
  have hb : a ∈ attr b := by
    simpa [hab] using ha
  exact h (by simpa [attr] using hb)

end Stage

/-- CT task: absorption/excitation (bulk ground → bulk excited). -/
def absorptionTask : Constructor.CT.Task Stage :=
  { arcs := [(Stage.attr .bulkGround, Stage.attr .bulkExcited)] }

/-- CT task: transport (bulk excited → surface). -/
def transportTask : Constructor.CT.Task Stage :=
  { arcs := [(Stage.attr .bulkExcited, Stage.attr .surface)] }

/-- CT task: emission (surface → vacuum). -/
def emissionTask : Constructor.CT.Task Stage :=
  { arcs := [(Stage.attr .surface, Stage.attr .vacuum)] }

/-- CT task: full three-step photoemission (serial composition). -/
def fullPhotoemissionTask : Constructor.CT.Task Stage :=
  Constructor.CT.Task.seq absorptionTask (Constructor.CT.Task.seq transportTask emissionTask)

theorem absorptionTask_ne_transportTask : absorptionTask ≠ transportTask := by
  intro hEq
  have hArcs : absorptionTask.arcs = transportTask.arcs :=
    congrArg Constructor.CT.Task.arcs hEq
  have hList :
      [(Stage.attr .bulkGround, Stage.attr .bulkExcited)] =
        [(Stage.attr .bulkExcited, Stage.attr .surface)] := by
    simpa [absorptionTask, transportTask] using hArcs
  have hPair :
      (Stage.attr .bulkGround, Stage.attr .bulkExcited) =
        (Stage.attr .bulkExcited, Stage.attr .surface) := by
    simpa using hList
  have hAttr : Stage.attr .bulkGround = Stage.attr .bulkExcited :=
    congrArg Prod.fst hPair
  exact Stage.attr_ne (a := .bulkGround) (b := .bulkExcited) (by decide) hAttr

theorem absorptionTask_ne_emissionTask : absorptionTask ≠ emissionTask := by
  intro hEq
  have hArcs : absorptionTask.arcs = emissionTask.arcs :=
    congrArg Constructor.CT.Task.arcs hEq
  have hList :
      [(Stage.attr .bulkGround, Stage.attr .bulkExcited)] =
        [(Stage.attr .surface, Stage.attr .vacuum)] := by
    simpa [absorptionTask, emissionTask] using hArcs
  have hPair :
      (Stage.attr .bulkGround, Stage.attr .bulkExcited) =
        (Stage.attr .surface, Stage.attr .vacuum) := by
    simpa using hList
  have hAttr : Stage.attr .bulkGround = Stage.attr .surface :=
    congrArg Prod.fst hPair
  exact Stage.attr_ne (a := .bulkGround) (b := .surface) (by decide) hAttr

/-- Constructors for photoemission steps (plus serial/parallel composition). -/
inductive PhotonCtor (sys : PhotoemissionSystem)
  | absorb : AbsorptionTask sys → PhotonCtor sys
  | transport : TransportTask sys → PhotonCtor sys
  | emit : EmissionTask sys → PhotonCtor sys
  | seq : PhotonCtor sys → PhotonCtor sys → PhotonCtor sys
  | par : PhotonCtor sys → PhotonCtor sys → PhotonCtor sys

/-- Implementation relation: constructors implement named tasks subject to basic physical constraints. -/
inductive PhotonImplements (sys : PhotoemissionSystem) (photonEnergy bandGap : ℝ) :
    PhotonCtor sys → Constructor.CT.Task Stage → Prop
  | absorb (T₁ : AbsorptionTask sys) {T : Constructor.CT.Task Stage}
      (hT : T = absorptionTask)
      (hEnergy : bandGap ≤ photonEnergy)
      (hSpec : T₁.absorption_spec) :
      PhotonImplements sys photonEnergy bandGap (.absorb T₁) T
  | transport (T₂ : TransportTask sys) {T : Constructor.CT.Task Stage}
      (hT : T = transportTask)
      (hPos : 0 < T₂.mean_free_path)
      (hSpec : T₂.attenuation_model) :
      PhotonImplements sys photonEnergy bandGap (.transport T₂) T
  | emit (T₃ : EmissionTask sys) {T : Constructor.CT.Task Stage}
      (hT : T = emissionTask)
      (hPos : 0 < T₃.work_function)
      (hSpec : T₃.wkb_transmission) :
      PhotonImplements sys photonEnergy bandGap (.emit T₃) T
  | seq {c₁ c₂ : PhotonCtor sys} {T U : Constructor.CT.Task Stage}
      (h₁ : PhotonImplements sys photonEnergy bandGap c₁ T)
      (h₂ : PhotonImplements sys photonEnergy bandGap c₂ U) :
      PhotonImplements sys photonEnergy bandGap (.seq c₁ c₂) (Constructor.CT.Task.seq T U)
  | par {c₁ c₂ : PhotonCtor sys} {T U : Constructor.CT.Task Stage}
      (h₁ : PhotonImplements sys photonEnergy bandGap c₁ T)
      (h₂ : PhotonImplements sys photonEnergy bandGap c₂ U) :
      PhotonImplements sys photonEnergy bandGap (.par c₁ c₂) (Constructor.CT.Task.par T U)

namespace PhotonImplements

variable {sys : PhotoemissionSystem} {photonEnergy bandGap : ℝ}

theorem arcs_pos {c : PhotonCtor sys} {T : Constructor.CT.Task Stage}
    (h : PhotonImplements sys photonEnergy bandGap c T) :
    0 < T.arcs.length := by
  induction h with
  | absorb _ hT _ _ =>
      cases hT
      simp [absorptionTask]
  | transport _ hT _ _ =>
      cases hT
      simp [transportTask]
  | emit _ hT _ _ =>
      cases hT
      simp [emissionTask]
  | seq _ _ ih₁ ih₂ =>
      simpa [Constructor.CT.Task.seq, List.length_append] using Nat.add_pos_left ih₁ _
  | par _ _ ih₁ ih₂ =>
      simpa [Constructor.CT.Task.par, List.length_append] using Nat.add_pos_left ih₁ _

theorem length_gt_one_of_seq {c₁ c₂ : PhotonCtor sys} {T : Constructor.CT.Task Stage}
    (h : PhotonImplements sys photonEnergy bandGap (.seq c₁ c₂) T) :
    1 < T.arcs.length := by
  cases h with
  | seq h₁ h₂ =>
      rename_i T U
      have hpos₁ : 0 < T.arcs.length := arcs_pos h₁
      have hpos₂ : 0 < U.arcs.length := arcs_pos h₂
      have hle₁ : 1 ≤ T.arcs.length := Nat.succ_le_of_lt hpos₁
      have hle₂ : 1 ≤ U.arcs.length := Nat.succ_le_of_lt hpos₂
      have htwo : (2 : ℕ) ≤ T.arcs.length + U.arcs.length := by
        simpa using (Nat.add_le_add hle₁ hle₂)
      have : 1 < T.arcs.length + U.arcs.length :=
        lt_of_lt_of_le (by decide : (1 : ℕ) < 2) htwo
      simpa [Constructor.CT.Task.seq, List.length_append] using this

theorem length_gt_one_of_par {c₁ c₂ : PhotonCtor sys} {T : Constructor.CT.Task Stage}
    (h : PhotonImplements sys photonEnergy bandGap (.par c₁ c₂) T) :
    1 < T.arcs.length := by
  cases h with
  | par h₁ h₂ =>
      rename_i T U
      have hpos₁ : 0 < T.arcs.length := arcs_pos h₁
      have hpos₂ : 0 < U.arcs.length := arcs_pos h₂
      have hle₁ : 1 ≤ T.arcs.length := Nat.succ_le_of_lt hpos₁
      have hle₂ : 1 ≤ U.arcs.length := Nat.succ_le_of_lt hpos₂
      have htwo : (2 : ℕ) ≤ T.arcs.length + U.arcs.length := by
        simpa using (Nat.add_le_add hle₁ hle₂)
      have : 1 < T.arcs.length + U.arcs.length :=
        lt_of_lt_of_le (by decide : (1 : ℕ) < 2) htwo
      simpa [Constructor.CT.Task.par, List.length_append] using this

end PhotonImplements

/-- Photoemission as a `TaskCT` instance parameterized by an energy threshold. -/
def photoemissionTaskCT (sys : PhotoemissionSystem) (photonEnergy bandGap : ℝ) : TaskCT Stage :=
  { Ctor := PhotonCtor sys
    implements := PhotonImplements sys photonEnergy bandGap
    seqCtor := PhotonCtor.seq
    parCtor := PhotonCtor.par
    implements_seq := by
      intro c₁ c₂ T U h₁ h₂
      exact PhotonImplements.seq h₁ h₂
    implements_par := by
      intro c₁ c₂ T U h₁ h₂
      exact PhotonImplements.par h₁ h₂ }

namespace photoemissionTaskCT

variable {sys : PhotoemissionSystem} {photonEnergy bandGap : ℝ}

theorem possible_full_of_possible_steps
    (CT := photoemissionTaskCT sys photonEnergy bandGap)
    (h₁ : CT.possible absorptionTask)
    (h₂ : CT.possible transportTask)
    (h₃ : CT.possible emissionTask) :
    CT.possible fullPhotoemissionTask := by
  have h12 : CT.possible (Constructor.CT.Task.seq absorptionTask transportTask) :=
    CT.possible_seq h₁ h₂
  have h123 :
      CT.possible
        (Constructor.CT.Task.seq
          (Constructor.CT.Task.seq absorptionTask transportTask)
          emissionTask) :=
    CT.possible_seq h12 h₃
  simpa [fullPhotoemissionTask, Constructor.CT.Task.seq, List.append_assoc] using h123

end photoemissionTaskCT

/-- Energy threshold: if photon energy is below the band gap, absorption is CT-impossible. -/
theorem energy_conservation_required (sys : PhotoemissionSystem)
    (photonEnergy bandGap : ℝ)
    (h_insufficient : photonEnergy < bandGap) :
    (photoemissionTaskCT sys photonEnergy bandGap).impossible absorptionTask := by
  intro hPossible
  rcases hPossible with ⟨c, hc⟩
  cases c with
  | absorb T₁ =>
      cases hc with
      | absorb _ hT hEnergy _ =>
          cases hT
          exact (not_le_of_gt h_insufficient) hEnergy
  | transport =>
      cases hc with
      | transport _ hT _ _ =>
          exact absorptionTask_ne_transportTask hT
  | emit =>
      cases hc with
      | emit _ hT _ _ =>
          exact absorptionTask_ne_emissionTask hT
  | seq c₁ c₂ =>
      have hlen : 1 < absorptionTask.arcs.length :=
        PhotonImplements.length_gt_one_of_seq (sys:=sys) (photonEnergy:=photonEnergy)
          (bandGap:=bandGap) hc
      have : False := by
        have hlen' : 1 < absorptionTask.arcs.length := hlen
        simp [absorptionTask] at hlen'
      exact this
  | par c₁ c₂ =>
      have hlen : 1 < absorptionTask.arcs.length :=
        PhotonImplements.length_gt_one_of_par (sys:=sys) (photonEnergy:=photonEnergy)
          (bandGap:=bandGap) hc
      have : False := by
        have hlen' : 1 < absorptionTask.arcs.length := hlen
        simp [absorptionTask] at hlen'
      exact this

end Photoemission
end Physics
end HeytingLean
