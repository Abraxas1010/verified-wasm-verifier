import HeytingLean.Genesis.VirtualUntying
import HeytingLean.Genesis.Life

/-!
# Genesis.VirtualCoinductiveSemantics

Phase-K4 generalized coinductive virtual semantics over finite deterministic cycles.
-/

namespace HeytingLean.Genesis

open CoGame

/-- Deterministic successor on a finite cycle of size `n+1`. -/
def succOnFin (n : Nat) (i : Fin (Nat.succ n)) : Fin (Nat.succ n) :=
  ⟨(i.1 + 1) % Nat.succ n, Nat.mod_lt _ (Nat.succ_pos n)⟩

/-- Finite deterministic cycle co-game with symmetric left/right successor sets. -/
def cycleCoGame (n : Nat) : CoGame where
  Node := Fin (Nat.succ n)
  root := ⟨0, Nat.succ_pos n⟩
  leftSucc i := {j | j = succOnFin n i}
  rightSucc i := {j | j = succOnFin n i}

/-- Boolean phase dynamics induced by parity of the tick index. -/
def cyclePhaseAt (b : Bool) (k : Nat) : Bool :=
  if k % 2 = 0 then b else !b

@[simp] theorem cyclePhaseAt_zero (b : Bool) : cyclePhaseAt b 0 = b := by
  simp [cyclePhaseAt]

/-- Two-tick periodicity of the virtual phase dynamics. -/
theorem cyclePhaseAt_period2 (b : Bool) (k : Nat) : cyclePhaseAt b (k + 2) = cyclePhaseAt b k := by
  have hmod : (k + 2) % 2 = k % 2 := Nat.add_mod_right k 2
  simp [cyclePhaseAt, hmod]

/-- Two-phase projection (iterant) extracted from cycle dynamics at ticks `0` and `1`. -/
def evalCycle2 (init : Bool) : Iterant Bool :=
  ⟨cyclePhaseAt init 0, cyclePhaseAt init 1⟩

/-- K4 target: the 2-cycle semantics recovers the canonical Life iterant phases. -/
theorem evalCycle2_equiv_iterant (init : Bool) : evalCycle2 init = evalLife init := by
  cases init <;> simp [evalCycle2, evalLife, cyclePhaseAt, phaseI, phaseJ]

/-- General cycle-phase view (parameterized by cycle size). -/
def evalCycleNPhase (_n : Nat) (init : Bool) (k : Nat) : Bool :=
  cyclePhaseAt init k

/-- K4 target: generalized cycles retain period-2 phase behavior. -/
theorem evalCycleN_has_periodic_phase (n : Nat) (init : Bool) (k : Nat) :
    evalCycleNPhase n init (k + 2) = evalCycleNPhase n init k := by
  simp [evalCycleNPhase, cyclePhaseAt_period2]

/-- K4 target: unrolling finite cycles preserves the established depth-prefix semantics. -/
theorem unroll_preserves_prefix_semantics (n depth : Nat) :
    virtualInterpretUnroll depth (virtualUnroll depth (cycleCoGame n)) = nesting depth := by
  simpa [virtualInterpretUnroll, virtualUnroll] using
    interpretUnroll_eq_nesting depth (virtualUnroll depth (cycleCoGame n))

/-- `Life` appears as the one-node cycle special case (`n = 0`) up to bisimulation. -/
theorem life_as_cycle_special_case : CoGame.Bisim (cycleCoGame 0) CoGame.Life := by
  refine ⟨fun _ _ => True, ?_⟩
  refine CoGame.IsBisim.mk ?_ ?_ ?_ ?_ ?_
  · trivial
  · intro x y hxy x' hx'
    refine ⟨(), ?_, trivial⟩
    change () = ()
    rfl
  · intro x y hxy y' hy'
    refine ⟨succOnFin 0 x, ?_, trivial⟩
    rfl
  · intro x y hxy x' hx'
    refine ⟨(), ?_, trivial⟩
    change () = ()
    rfl
  · intro x y hxy y' hy'
    refine ⟨succOnFin 0 x, ?_, trivial⟩
    rfl

end HeytingLean.Genesis
