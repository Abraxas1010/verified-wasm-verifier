import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic

namespace HeytingLean.Bridge.NoCoincidence.Basic

/-- A `3n`-bit reversible state, encoded as a finite index.
Neyman §2 studies reversible maps `C : {0,1}^{3n} → {0,1}^{3n}`. -/
abbrev State (n : ℕ) := Fin (2 ^ (3 * n))

/-- A reversible gate on the `3n`-bit state space, presented by forward and backward maps.
Neyman §2 emphasizes bijective gate semantics rather than partial transition rules. -/
structure RevGate (n : ℕ) where
  forward : State n → State n
  backward : State n → State n
  left_inv : ∀ x, backward (forward x) = x
  right_inv : ∀ x, forward (backward x) = x

namespace RevGate

/-- Identity reversible gate. -/
def id (n : ℕ) : RevGate n where
  forward := fun x => x
  backward := fun x => x
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

/-- Composition of reversible gates. -/
def comp (g h : RevGate n) : RevGate n where
  forward := h.forward ∘ g.forward
  backward := g.backward ∘ h.backward
  left_inv := by
    intro x
    simp [Function.comp, h.left_inv, g.left_inv]
  right_inv := by
    intro x
    simp [Function.comp, h.right_inv, g.right_inv]

private def six : State 1 := ⟨6, by decide⟩
private def seven : State 1 := ⟨7, by decide⟩

/-- The 3-bit Toffoli gate. In binary it swaps `110` and `111`, fixing all other states.
This is the standard reversible-control gate cited by Neyman (§2, footnote 2). -/
def toffoliGate : RevGate 1 where
  forward := fun x =>
    if x = six then seven else if x = seven then six else x
  backward := fun x =>
    if x = six then seven else if x = seven then six else x
  left_inv := by
    intro x
    by_cases hx6 : x = six
    · subst hx6
      simp [six, seven]
    · by_cases hx7 : x = seven
      · subst hx7
        simp [six, seven]
      · simp [hx6, hx7]
  right_inv := by
    intro x
    by_cases hx6 : x = six
    · subst hx6
      simp [six, seven]
    · by_cases hx7 : x = seven
      · subst hx7
        simp [six, seven]
      · simp [hx6, hx7]

private theorem exponent_pos (n : ℕ) (hn : 0 < n) : 0 < 3 * n := by
  omega

private theorem xor_one_lt_stateCard (n : ℕ) (hn : 0 < n) (x : State n) :
    x.1 ^^^ 1 < 2 ^ (3 * n) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (exponent_pos n hn))
  have hx : x.1 < 2 ^ (k + 1) := by
    simpa [hk] using x.2
  have hdiv : Nat.div2 x.1 < 2 ^ k := by
    have hbit : Nat.bit (Nat.bodd x.1) (Nat.div2 x.1) < 2 ^ (k + 1) := by
      simpa [Nat.bit_bodd_div2] using hx
    exact (Nat.bit_lt_two_pow_succ_iff (b := Nat.bodd x.1) (x := Nat.div2 x.1) (n := k)).1 hbit
  have hxor :
      x.1 ^^^ 1 = Nat.bit (not (Nat.bodd x.1)) (Nat.div2 x.1) := by
    calc
      x.1 ^^^ 1
          = Nat.bit (Nat.bodd x.1) (Nat.div2 x.1) ^^^ Nat.bit true 0 := by
              simp [Nat.bit_bodd_div2]
      _ = Nat.bit (bne (Nat.bodd x.1) true) (Nat.div2 x.1 ^^^ 0) := by
            simpa using Nat.xor_bit (Nat.bodd x.1) (Nat.div2 x.1) true 0
      _ = Nat.bit (not (Nat.bodd x.1)) (Nat.div2 x.1) := by
            simp
  have hbit :
      Nat.bit (!(Nat.bodd x.1)) (Nat.div2 x.1) < 2 ^ (k + 1) :=
    (Nat.bit_lt_two_pow_succ_iff (b := !(Nat.bodd x.1)) (x := Nat.div2 x.1) (n := k)).2 hdiv
  simpa [hk, hxor] using hbit

/-- Toggle the least significant bit. This is the key concrete witness gate used in tests:
it is reversible, involutive, and destroys a trailing all-zero suffix whenever `n > 0`. -/
def toggleLowBitGate (n : ℕ) (hn : 0 < n) : RevGate n where
  forward := fun x => ⟨x.1 ^^^ 1, xor_one_lt_stateCard n hn x⟩
  backward := fun x => ⟨x.1 ^^^ 1, xor_one_lt_stateCard n hn x⟩
  left_inv := by
    intro x
    apply Fin.ext
    simp [Nat.xor_assoc]
  right_inv := by
    intro x
    apply Fin.ext
    simp [Nat.xor_assoc]

end RevGate

/-- A reversible circuit is a finite composition of reversible gates.
This keeps evaluation total and makes bijectivity a theorem of composition. -/
structure RevCircuit (n : ℕ) where
  steps : List (RevGate n)

namespace RevCircuit

/-- Evaluate a list of reversible gates by composition. -/
def evalSteps (gs : List (RevGate n)) : State n → State n
  | x =>
    match gs with
    | [] => x
    | g :: rest => evalSteps rest (g.forward x)

/-- Evaluate the inverse circuit by reversing the gate list. -/
def evalInvSteps (gs : List (RevGate n)) : State n → State n
  | x =>
    match gs with
    | [] => x
    | g :: rest => g.backward (evalInvSteps rest x)

/-- Circuit evaluation. -/
def eval (C : RevCircuit n) : State n → State n :=
  evalSteps C.steps

/-- Inverse circuit evaluation. -/
def evalInv (C : RevCircuit n) : State n → State n :=
  evalInvSteps C.steps

theorem evalInv_left_steps (gs : List (RevGate n)) :
    ∀ x, evalInvSteps gs (evalSteps gs x) = x := by
  intro x
  induction gs generalizing x with
  | nil =>
      rfl
  | cons g rest ih =>
      simp [evalSteps, evalInvSteps, ih, g.left_inv]

theorem evalInv_right_steps (gs : List (RevGate n)) :
    ∀ x, evalSteps gs (evalInvSteps gs x) = x := by
  intro x
  induction gs generalizing x with
  | nil =>
      rfl
  | cons g rest ih =>
      simp [evalSteps, evalInvSteps, ih, g.right_inv]

theorem eval_left_inv (C : RevCircuit n) : ∀ x, C.evalInv (C.eval x) = x :=
  evalInv_left_steps C.steps

theorem eval_right_inv (C : RevCircuit n) : ∀ x, C.eval (C.evalInv x) = x :=
  evalInv_right_steps C.steps

/-- Evaluation of a reversible circuit is bijective. -/
theorem eval_bijective (C : RevCircuit n) : Function.Bijective C.eval := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have hx := congrArg C.evalInv hxy
    simpa [C.eval_left_inv x, C.eval_left_inv y] using hx
  · intro y
    refine ⟨C.evalInv y, C.eval_right_inv y⟩

/-- The empty circuit is the identity. -/
def identity (n : ℕ) : RevCircuit n where
  steps := []

/-- Singleton circuit from one reversible gate. -/
def singleton (g : RevGate n) : RevCircuit n where
  steps := [g]

/-- Structural size of a reversible circuit. -/
def size (C : RevCircuit n) : ℕ :=
  C.steps.length

/-- A concrete witness circuit that flips the low bit on every state. -/
def lowBitToggleCircuit (n : ℕ) (hn : 0 < n) : RevCircuit n :=
  singleton (RevGate.toggleLowBitGate n hn)

end RevCircuit

end HeytingLean.Bridge.NoCoincidence.Basic
