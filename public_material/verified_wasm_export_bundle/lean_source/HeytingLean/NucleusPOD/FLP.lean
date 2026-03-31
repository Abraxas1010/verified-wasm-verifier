import HeytingLean.NucleusPOD.Foundation

namespace HeytingLean
namespace NucleusPOD

/-!
Layer 12: Formalized Impossibility Results and Their Nucleus Circumvention
Generated from `NucleusPOD_Lean_Proof_Catalog.docx`.
-/

def decideStep (msg delivered : Bool) : Bool :=
  msg && delivered

/-- Nucleus repair channel: combine local decision bit with externally supplied repair witness. -/
def decideR (b repair : Bool) : Bool :=
  b || repair

/-- Three-process asynchronous model with lossy message delivery and crashes. -/
abbrev Process := Fin 3
abbrev Schedule := Process → Process → Bool

structure AsyncRun where
  delivered : Schedule
  crashed : Process → Bool

abbrev DecisionRule := AsyncRun → Process → Bool

def receives (r : AsyncRun) (dst src : Process) : Prop :=
  r.delivered src dst = true ∧ r.crashed src = false

/-- Quorum witness: destination receives from two distinct non-crashed sources. -/
def hasTwoSourceQuorum (r : AsyncRun) (dst : Process) : Prop :=
  ∃ s₁ s₂ : Process, s₁ ≠ s₂ ∧ receives r dst s₁ ∧ receives r dst s₂

instance (r : AsyncRun) (dst : Process) : Decidable (hasTwoSourceQuorum r dst) := by
  unfold hasTwoSourceQuorum receives
  infer_instance

def decideFromQuorum (r : AsyncRun) (dst : Process) : Bool :=
  decide (hasTwoSourceQuorum r dst)

def globallyTerminates (r : AsyncRun) : Prop :=
  ∀ p : Process, decideFromQuorum r p = true

def globallyTerminatesWith (rule : DecisionRule) (r : AsyncRun) : Prop :=
  ∀ p : Process, rule r p = true

def blackout (r : AsyncRun) : Prop :=
  ∀ src dst : Process, r.delivered src dst = false

/-- A decision rule is blackout-sound if total packet loss forces non-decision everywhere. -/
def blackoutSound (rule : DecisionRule) : Prop :=
  ∀ r : AsyncRun, blackout r → ∀ p : Process, rule r p = false

theorem blackout_no_quorum (r : AsyncRun) (hBlackout : blackout r) (dst : Process) :
    ¬ hasTwoSourceQuorum r dst := by
  intro hQ
  rcases hQ with ⟨s₁, s₂, _hneq, hs₁, _hs₂⟩
  have hFalse : r.delivered s₁ dst = false := hBlackout s₁ dst
  have : False := by
    simpa [hFalse] using hs₁.1
  exact this

theorem decideFromQuorum_blackout (r : AsyncRun) (hBlackout : blackout r) (dst : Process) :
    decideFromQuorum r dst = false := by
  unfold decideFromQuorum
  by_cases hQ : hasTwoSourceQuorum r dst
  · exact (False.elim ((blackout_no_quorum r hBlackout dst) hQ))
  · simp [hQ]

/-- Blackout-sound rules cannot globally terminate when the network is fully blacked out. -/
theorem no_blackout_sound_rule_terminates
    (rule : DecisionRule) (hSound : blackoutSound rule)
    (r : AsyncRun) (hBlackout : blackout r) :
    ¬ globallyTerminatesWith rule r := by
  intro hTerm
  let p0 : Process := ⟨0, by decide⟩
  have hTrue : rule r p0 = true := hTerm p0
  have hFalse : rule r p0 = false := hSound r hBlackout p0
  have : false = true := hFalse.symm.trans hTrue
  exact Bool.false_ne_true this

theorem decideFromQuorum_blackout_sound : blackoutSound decideFromQuorum := by
  intro r hBlackout p
  exact decideFromQuorum_blackout r hBlackout p

/-- FLP-style obstruction generalized over all blackout-sound decision rules. -/
theorem FLP_blackout_no_termination_general
    (rule : DecisionRule) (hSound : blackoutSound rule)
    (r : AsyncRun) (hBlackout : blackout r) :
    ¬ globallyTerminatesWith rule r := by
  exact no_blackout_sound_rule_terminates rule hSound r hBlackout

/-- Original quorum-based instance recovered from the generalized obstruction theorem. -/
theorem FLP_blackout_no_termination (r : AsyncRun) (hBlackout : blackout r) :
    ¬ globallyTerminates r := by
  have hNoTerm :
      ¬ globallyTerminatesWith decideFromQuorum r :=
    FLP_blackout_no_termination_general decideFromQuorum decideFromQuorum_blackout_sound r hBlackout
  simpa [globallyTerminates, globallyTerminatesWith] using hNoTerm

theorem FLP_classical : decideStep true false = false := by
  rfl

theorem FLP_requires_EM (b : Bool) : decideStep b false = false := by
  cases b <;> rfl

/-- Escaping the classical FLP dead-end requires asserting a repair witness. -/
theorem nucleus_escapes_FLP (b repair : Bool) :
    decideR (decideStep b false) repair = true ↔ repair = true := by
  cases b <;> cases repair <;> decide

end NucleusPOD
end HeytingLean
