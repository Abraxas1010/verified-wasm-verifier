import HeytingLean.PerspectivalPlenum.StrictRatchet.Contracts
import HeytingLean.PerspectivalPlenum.StrictRatchet.Separation

namespace HeytingLean
namespace PerspectivalPlenum
namespace StrictRatchet

/-- Gate G1: all claimed lanes have machine-checked soundness contracts. -/
def GateG1 : Prop :=
  Contracts.soundnessCoverage

/-- Gate G2: all claimed lanes expose exact conservativity or scoped-loss conservativity. -/
def GateG2 : Prop :=
  Contracts.conservativityCoverage

/-- Explicit strict edge in the parallel strict-ratchet lane (base -> witness). -/
theorem strict_edge_base_to_witness
    {α : Type} [Order.Frame α]
    (S : RatchetStep α) (J : Nucleus α) :
    StrictStage.strictlyPrecedes (StrictStage.base J) (StrictStage.witness S J) := by
  simp [StrictStage.strictlyPrecedes, StrictStage.base, StrictStage.witness]

/-- Explicit strict edge in the parallel strict-ratchet lane (witness -> plenum). -/
theorem strict_edge_witness_to_plenum
    {α : Type} [Order.Frame α]
    (S : RatchetStep α) (steps : List (RatchetStep α)) (J : Nucleus α) :
    StrictStage.strictlyPrecedes (StrictStage.witness S J) (StrictStage.plenum steps J) := by
  simp [StrictStage.strictlyPrecedes, StrictStage.witness, StrictStage.plenum]

/-- Proposition `P`: strict-lane separation witness at the plenum stage. -/
def P : Prop :=
  separationWitness StrictLevel.L2

/-- Proposition `Q`: legacy single-step tower is non-strict after stage 1. -/
def Q : Prop :=
  ∀ {α : Type} [Order.Frame α] (S : RatchetStep α) (J : Nucleus α),
    RatchetStep.iterate S 2 J = RatchetStep.iterate S 1 J

theorem P_holds : P :=
  separationWitness_L2

theorem Q_holds : Q := by
  intro α _ S J
  exact RatchetStep.iterate_two_eq_one S J

/-- Gate G3: stage chain is explicit, and separation/non-strict witnesses are explicit propositions. -/
def GateG3 : Prop :=
  (∀ {α : Type} [Order.Frame α] (S : RatchetStep α) (J : Nucleus α),
      StrictStage.strictlyPrecedes (StrictStage.base J) (StrictStage.witness S J)) ∧
    (∀ {α : Type} [Order.Frame α] (S : RatchetStep α)
      (steps : List (RatchetStep α)) (J : Nucleus α),
      StrictStage.strictlyPrecedes (StrictStage.witness S J) (StrictStage.plenum steps J)) ∧
    P ∧ Q

theorem GateG1_complete : GateG1 :=
  Contracts.soundnessCoverage_complete

theorem GateG2_complete : GateG2 :=
  Contracts.conservativityCoverage_complete

theorem GateG3_complete : GateG3 := by
  refine ⟨?_, ?_, P_holds, Q_holds⟩
  · intro α _ S J
    exact strict_edge_base_to_witness S J
  · intro α _ S steps J
    exact strict_edge_witness_to_plenum S steps J

/-- Strictness ledger entry classification for audit artifacts. -/
inductive EdgeClass where
  | strict
  | nonStrict
  deriving DecidableEq, Repr

/-- Machine-checkable strictness ledger entry. -/
structure StrictnessLedgerEntry where
  edgeId : String
  edgeClass : EdgeClass
  witness : Prop
  proved : witness

/-- Lean-level strictness ledger backing the external JSON status artifact. -/
def strictnessLedger : List StrictnessLedgerEntry :=
  [ { edgeId := "strict_base_to_witness"
      edgeClass := .strict
      witness := ∀ {α : Type} [Order.Frame α] (S : RatchetStep α) (J : Nucleus α),
        StrictStage.strictlyPrecedes (StrictStage.base J) (StrictStage.witness S J)
      proved := by
        intro α _ S J
        exact strict_edge_base_to_witness S J }
  , { edgeId := "strict_witness_to_plenum"
      edgeClass := .strict
      witness := ∀ {α : Type} [Order.Frame α] (S : RatchetStep α)
        (steps : List (RatchetStep α)) (J : Nucleus α),
          StrictStage.strictlyPrecedes (StrictStage.witness S J) (StrictStage.plenum steps J)
      proved := by
        intro α _ S steps J
        exact strict_edge_witness_to_plenum S steps J }
  , { edgeId := "legacy_iterate_non_strict_after_stage1"
      edgeClass := .nonStrict
      witness := Q
      proved := Q_holds }
  ]

/-- Global closure statement for this phase. -/
def AllGatesClosed : Prop :=
  GateG1 ∧ GateG2 ∧ GateG3

theorem allGatesClosed_complete : AllGatesClosed := by
  exact ⟨GateG1_complete, GateG2_complete, GateG3_complete⟩

end StrictRatchet
end PerspectivalPlenum
end HeytingLean
