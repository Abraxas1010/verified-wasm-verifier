import Mathlib.Data.Finset.Max
import Mathlib.Tactic.NormNum
import HeytingLean.Epiplexity.Core
import HeytingLean.Quantum.LoFCircuit

/-!
# Quantum (LoF-circuit) epiplexity — finite bridge

This module provides a small, finite interface between the deterministic LoF-circuit model
(`HeytingLean.Quantum.LoFCircuit`) and the finite-only Epiplexity core (`FinDist`-based MDL).

It is intentionally conservative:
- no amplitudes / no probabilistic measurement semantics,
- we work on a closed, finite subset of Bloch-like states (the 6 axis points).
-/

namespace HeytingLean
namespace Epiplexity
namespace Quantum

open scoped BigOperators

noncomputable section

open HeytingLean.Meta.AIT
open HeytingLean.Probability.InfoTheory
open HeytingLean.Epiplexity.Info

/-! ## A finite closed subset of `Quantum.LoFState` -/

/-- The six axis points `±X, ±Y, ±Z` (a finite closed subset under the given gate actions). -/
inductive AxisState where
  | Xp | Xm | Yp | Ym | Zp | Zm
deriving DecidableEq, Repr

instance : Fintype AxisState where
  elems := {AxisState.Xp, AxisState.Xm, AxisState.Yp, AxisState.Ym, AxisState.Zp, AxisState.Zm}
  complete := by
    intro a
    cases a <;> simp

instance : Nonempty AxisState := ⟨AxisState.Zp⟩

/-- Embed an `AxisState` into the ambient Bloch-style `LoFState` (`ℝ³`). -/
def AxisState.toLoFState : AxisState → HeytingLean.Quantum.LoFState
  | .Xp => ⟨1, 0, 0⟩
  | .Xm => ⟨-1, 0, 0⟩
  | .Yp => ⟨0, 1, 0⟩
  | .Ym => ⟨0, -1, 0⟩
  | .Zp => HeytingLean.Quantum.LoFState.void
  | .Zm => HeytingLean.Quantum.LoFState.markState

/-! ## Gate/circuit semantics on `AxisState` -/

/-- Gate action restricted to `AxisState`, consistent with `Quantum.gateX/Y/Z/H` on the embedding. -/
def applyGateAxis : HeytingLean.Quantum.LoFGate → AxisState → AxisState
  | .X, .Xp => .Xp
  | .X, .Xm => .Xm
  | .X, .Yp => .Ym
  | .X, .Ym => .Yp
  | .X, .Zp => .Zm
  | .X, .Zm => .Zp
  | .Y, .Xp => .Xm
  | .Y, .Xm => .Xp
  | .Y, .Yp => .Yp
  | .Y, .Ym => .Ym
  | .Y, .Zp => .Zm
  | .Y, .Zm => .Zp
  | .Z, .Xp => .Xm
  | .Z, .Xm => .Xp
  | .Z, .Yp => .Ym
  | .Z, .Ym => .Yp
  | .Z, .Zp => .Zp
  | .Z, .Zm => .Zm
  | .H, .Xp => .Zp
  | .H, .Xm => .Zm
  | .H, .Yp => .Ym
  | .H, .Ym => .Yp
  | .H, .Zp => .Xp
  | .H, .Zm => .Xm

theorem applyGateAxis_involutive (g : HeytingLean.Quantum.LoFGate) :
    Function.Involutive (applyGateAxis g) := by
  intro s
  cases g <;> cases s <;> rfl

/-- Circuit execution on `AxisState` (same fold order as `Quantum.runCircuit`). -/
def runCircuitAxis : HeytingLean.Quantum.Circuit → AxisState → AxisState
  | [], s => s
  | g :: cs, s => runCircuitAxis cs (applyGateAxis g s)

theorem runCircuitAxis_append (c₁ c₂ : HeytingLean.Quantum.Circuit) (s : AxisState) :
    runCircuitAxis (c₁ ++ c₂) s = runCircuitAxis c₂ (runCircuitAxis c₁ s) := by
  induction c₁ generalizing s with
  | nil =>
      simp [runCircuitAxis]
  | cons g gs ih =>
      simp [runCircuitAxis, ih]

theorem runCircuitAxis_reverse_run (c : HeytingLean.Quantum.Circuit) (s : AxisState) :
    runCircuitAxis c.reverse (runCircuitAxis c s) = s := by
  induction c generalizing s with
  | nil =>
      simp [runCircuitAxis]
  | cons g cs ih =>
      calc
        runCircuitAxis (List.reverse (g :: cs)) (runCircuitAxis (g :: cs) s)
            = runCircuitAxis (cs.reverse ++ [g]) (runCircuitAxis cs (applyGateAxis g s)) := by
                simp [runCircuitAxis, List.reverse_cons]
        _ = runCircuitAxis [g] (runCircuitAxis cs.reverse (runCircuitAxis cs (applyGateAxis g s))) := by
              exact
                runCircuitAxis_append (c₁ := cs.reverse) (c₂ := [g])
                  (s := runCircuitAxis cs (applyGateAxis g s))
        _ = runCircuitAxis [g] (applyGateAxis g s) := by
              simp [ih]
        _ = applyGateAxis g (applyGateAxis g s) := by
              simp [runCircuitAxis]
        _ = s := (applyGateAxis_involutive g) s

theorem runCircuitAxis_surjective (c : HeytingLean.Quantum.Circuit) :
    Function.Surjective (runCircuitAxis c) := by
  intro t
  refine ⟨runCircuitAxis c.reverse t, ?_⟩
  -- Apply `run(reverse c) ∘ run(c) = id` to `c.reverse`, then simplify.
  simpa [List.reverse_reverse] using (runCircuitAxis_reverse_run (c := c.reverse) (s := t))

/-! ## A small positive seed distribution on `AxisState` -/

noncomputable def seedPmf : AxisState → ℝ
  | .Zp => (1 : ℝ) / 2
  | .Zm => (1 : ℝ) / 4
  | .Xp => (1 : ℝ) / 8
  | .Xm => (1 : ℝ) / 16
  | .Yp => (1 : ℝ) / 32
  | .Ym => (1 : ℝ) / 32

noncomputable def seedDist : FinDist AxisState where
  pmf := seedPmf
  nonneg := by
    intro s
    cases s <;> norm_num [seedPmf]
  sum_one := by
    classical
    -- Expand the finite sum over the six constructors and compute.
    change (({AxisState.Xp, AxisState.Xm, AxisState.Yp, AxisState.Ym, AxisState.Zp, AxisState.Zm} : Finset AxisState).sum seedPmf) = 1
    simp [seedPmf]
    norm_num

theorem seedDist_Pos : seedDist.Pos := by
  intro s
  cases s <;> norm_num [seedDist, seedPmf]

/-! ## From circuits to Epiplexity programs -/

theorem map_Pos_of_surjective
    {α β : Type u} [Fintype α] [Fintype β]
    (P : FinDist α) (hP : P.Pos) (f : α → β) (hf : Function.Surjective f) :
    (FinDist.map f P).Pos := by
  classical
  intro b
  rcases hf b with ⟨a0, rfl⟩
  have hterm_pos : 0 < (if f a0 = f a0 then P.pmf a0 else 0) := by
    simp [hP a0]
  have hnonneg : ∀ a : α, 0 ≤ if f a = f a0 then P.pmf a else 0 := by
    intro a
    by_cases h : f a = f a0 <;> simp [h, P.nonneg a]
  have hle :
      (if f a0 = f a0 then P.pmf a0 else 0)
        ≤ ∑ a : α, if f a = f a0 then P.pmf a else 0 := by
    have :=
      Finset.single_le_sum (s := (Finset.univ : Finset α))
        (f := fun a : α => if f a = f a0 then P.pmf a else 0)
        (a := a0) (fun a _ => hnonneg a) (by simp)
    simpa using this
  exact lt_of_lt_of_le hterm_pos hle

noncomputable def circuitDist (c : HeytingLean.Quantum.Circuit) : FinDist AxisState :=
  FinDist.map (f := runCircuitAxis c) seedDist

theorem circuitDist_Pos (c : HeytingLean.Quantum.Circuit) : (circuitDist c).Pos := by
  classical
  refine map_Pos_of_surjective (P := seedDist) seedDist_Pos (f := runCircuitAxis c)
    (runCircuitAxis_surjective (c := c))

/-- Fixed 2-bit encoding of a gate. -/
def encodeGate : HeytingLean.Quantum.LoFGate → Program
  | .X => [false, false]
  | .Y => [false, true]
  | .Z => [true, false]
  | .H => [true, true]

/-- Encode a circuit by concatenating 2-bit encodings of its gates. -/
def encodeCircuit : HeytingLean.Quantum.Circuit → Program
  | [] => []
  | g :: cs => encodeGate g ++ encodeCircuit cs

theorem encodeCircuit_codeLength (c : HeytingLean.Quantum.Circuit) :
    codeLength (encodeCircuit c) = 2 * c.length := by
  induction c with
  | nil =>
      simp [encodeCircuit, codeLength]
  | cons g cs ih =>
      have hgate : codeLength (encodeGate g) = 2 := by
        cases g <;> rfl
      calc
        codeLength (encodeCircuit (g :: cs))
            = codeLength (encodeGate g ++ encodeCircuit cs) := rfl
        _ = codeLength (encodeGate g) + codeLength (encodeCircuit cs) := by
              simp [codeLength, Program.length, List.length_append]
        _ = 2 + 2 * cs.length := by
              simp [hgate, ih]
        _ = 2 * (cs.length + 1) := by
              calc
                2 + 2 * cs.length = 2 * cs.length + 2 := (Nat.add_comm 2 (2 * cs.length))
                _ = 2 * (cs.length + 1) := by simp [Nat.mul_succ]
        _ = 2 * (List.length (g :: cs)) := by simp

/-- Interpret a circuit as an Epiplexity `Prog` over `AxisState`. -/
noncomputable def circuitProg (c : HeytingLean.Quantum.Circuit) : Epiplexity.Prog AxisState where
  code := encodeCircuit c
  runtime := c.length
  dist := circuitDist c
  distPos := circuitDist_Pos c

theorem circuitProg_feasible_iff (T : Nat) (c : HeytingLean.Quantum.Circuit) :
    Epiplexity.Prog.Feasible T (circuitProg c) ↔ c.length ≤ T := by
  rfl

/-! ## Optimal quantum programs (finite candidate sets) -/

abbrev QuantumMDLCost (X : FinDist AxisState) (c : HeytingLean.Quantum.Circuit) : ℝ :=
  mdlCost X (circuitProg c)

/-- An optimal quantum program chosen from a finite candidate set. -/
structure OptimalQuantumProgIn (T : Nat) (X : FinDist AxisState) (C : Finset HeytingLean.Quantum.Circuit) where
  c : HeytingLean.Quantum.Circuit
  mem : c ∈ C
  feasible : c.length ≤ T
  optimal :
    ∀ d : HeytingLean.Quantum.Circuit, d ∈ C → d.length ≤ T →
      QuantumMDLCost X c ≤ QuantumMDLCost X d

namespace OptimalQuantumProgIn

variable {T : Nat} {X : FinDist AxisState} {C : Finset HeytingLean.Quantum.Circuit}

/-- Quantum epiplexity `S_T^Q(X)` for an explicit optimizer witness. -/
def ST (opt : OptimalQuantumProgIn (T := T) (X := X) (C := C)) : Nat :=
  (circuitProg opt.c).codeLen

/-- Quantum time-bounded entropy `H_T^Q(X)` for an explicit optimizer witness. -/
def HT (opt : OptimalQuantumProgIn (T := T) (X := X) (C := C)) : ℝ :=
  crossEntropyBits X (circuitProg opt.c).dist

/-- Total quantum MDL value `MDL_T^Q(X) = S_T^Q(X) + H_T^Q(X)`. -/
def MDLT (opt : OptimalQuantumProgIn (T := T) (X := X) (C := C)) : ℝ :=
  (opt.ST : ℝ) + opt.HT

@[simp] theorem MDLT_eq_mdlCost (opt : OptimalQuantumProgIn (T := T) (X := X) (C := C)) :
    opt.MDLT = QuantumMDLCost X opt.c := by
  rfl

end OptimalQuantumProgIn

theorem nonempty_optimalQuantumProgIn_of_filter_nonempty
    (T : Nat) (X : FinDist AxisState) (C : Finset HeytingLean.Quantum.Circuit)
    (h : (C.filter (fun c => c.length ≤ T)).Nonempty) :
    Nonempty (OptimalQuantumProgIn (T := T) (X := X) (C := C)) := by
  classical
  let C0 : Finset HeytingLean.Quantum.Circuit := C.filter (fun c => c.length ≤ T)
  have hC0 : C0.Nonempty := h
  rcases Finset.exists_min_image C0 (QuantumMDLCost X) hC0 with ⟨c, hc0, hcmin⟩
  have hc_mem : c ∈ C := (Finset.mem_filter.1 hc0).1
  have hc_feas : c.length ≤ T := (Finset.mem_filter.1 hc0).2
  refine ⟨{ c := c, mem := hc_mem, feasible := hc_feas, optimal := ?_ }⟩
  intro d hdC hdFeas
  have hd0 : d ∈ C0 := Finset.mem_filter.2 ⟨hdC, hdFeas⟩
  exact hcmin d hd0

end

end Quantum
end Epiplexity
end HeytingLean
