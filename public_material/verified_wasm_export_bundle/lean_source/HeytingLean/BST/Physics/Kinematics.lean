import HeytingLean.BST.Analysis

/-!
# BST.Physics.Kinematics

Finite one-dimensional kinematics over the bounded `RealB` grid.
-/

namespace HeytingLean.BST.Physics

open HeytingLean.BST
open HeytingLean.BST.Analysis

structure State (k : ℕ) where
  pos : RealB k
  vel : RealB k
  deriving DecidableEq, Repr

def rest (k : ℕ) : State k where
  pos := RealB.default k
  vel := RealB.default k

def advance (k : ℕ) (hk : 0 < k) (dt acc : RealB k) (s : State k) : State k where
  pos := eulerStep k hk dt (fun _ => s.vel) s.pos
  vel := eulerStep k hk dt (fun _ => acc) s.vel

def advanceSteps (k : ℕ) (hk : 0 < k) (dt acc : RealB k) : ℕ → State k → State k
  | 0, s => s
  | n + 1, s => advanceSteps k hk dt acc n (advance k hk dt acc s)

def speedSquared (k : ℕ) (hk : 0 < k) (s : State k) : Rat :=
  square k hk s.vel

def kineticEnergy (k : ℕ) (hk : 0 < k) (s : State k) : Rat :=
  ((1 : Rat) / 2) * speedSquared k hk s

@[simp] theorem advance_zero_dt (k : ℕ) (hk : 0 < k)
    (acc : RealB k) (s : State k) :
    advance k hk (RealB.default k) acc s = s := by
  cases s
  simp [advance]

@[simp] theorem advance_zero_acc_vel (k : ℕ) (hk : 0 < k)
    (dt : RealB k) (s : State k) :
    (advance k hk dt (RealB.default k) s).vel = s.vel := by
  cases s
  simp [advance]

@[simp] theorem advance_rest_zero_acc (k : ℕ) (hk : 0 < k) (dt : RealB k) :
    advance k hk dt (RealB.default k) (rest k) = rest k := by
  simp [advance, rest]

@[simp] theorem advanceSteps_zero (k : ℕ) (hk : 0 < k)
    (dt acc : RealB k) (s : State k) :
    advanceSteps k hk dt acc 0 s = s := by
  rfl

theorem advanceSteps_rest_zero_acc (k : ℕ) (hk : 0 < k)
    (dt : RealB k) (n : ℕ) :
    advanceSteps k hk dt (RealB.default k) n (rest k) = rest k := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [advanceSteps, ih]

@[simp] theorem speedSquared_rest (k : ℕ) (hk : 0 < k) :
    speedSquared k hk (rest k) = 0 := by
  simp [speedSquared, rest, square]

theorem kineticEnergy_eq_half_speedSquared (k : ℕ) (hk : 0 < k) (s : State k) :
    kineticEnergy k hk s = ((1 : Rat) / 2) * speedSquared k hk s := by
  rfl

theorem kineticEnergy_nonneg (k : ℕ) (hk : 0 < k) (s : State k) :
    0 ≤ kineticEnergy k hk s := by
  unfold kineticEnergy
  have hs : 0 ≤ speedSquared k hk s := by
    unfold speedSquared
    exact square_nonneg k hk s.vel
  nlinarith

@[simp] theorem kineticEnergy_rest (k : ℕ) (hk : 0 < k) :
    kineticEnergy k hk (rest k) = 0 := by
  simp [kineticEnergy, speedSquared_rest]

end HeytingLean.BST.Physics
