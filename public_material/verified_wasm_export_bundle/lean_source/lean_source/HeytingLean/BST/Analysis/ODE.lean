import HeytingLean.BST.Numbers.Real

/-!
# BST.Analysis.ODE

Executable bounded Euler integration on `RealB`.
-/

namespace HeytingLean.BST.Analysis

open HeytingLean.BST

def eulerStep (k : ℕ) (hk : 0 < k) (dt : RealB k)
    (f : RealB k → RealB k) (x : RealB k) : RealB k :=
  RealB.add hk x (RealB.mul hk dt (f x))

def eulerSteps (k : ℕ) (hk : 0 < k) (dt : RealB k)
    (f : RealB k → RealB k) : ℕ → RealB k → RealB k
  | 0, x => x
  | n + 1, x => eulerSteps k hk dt f n (eulerStep k hk dt f x)

def eulerShadow (k : ℕ) (hk : 0 < k) (dt : RealB k)
    (f : RealB k → RealB k) : ℕ → RealB k → Rat
  | 0, x => RealB.toRat hk x
  | n + 1, x =>
      let xn := eulerSteps k hk dt f n x
      eulerShadow k hk dt f n x + RealB.toRat hk dt * RealB.toRat hk (f xn)

@[simp] theorem eulerStep_zero_dt (k : ℕ) (hk : 0 < k)
    (f : RealB k → RealB k) (x : RealB k) :
    eulerStep k hk (RealB.default k) f x = x := by
  simp [eulerStep]

@[simp] theorem eulerStep_zero_field (k : ℕ) (hk : 0 < k)
    (dt x : RealB k) :
    eulerStep k hk dt (fun _ => RealB.default k) x = x := by
  simp [eulerStep]

@[simp] theorem eulerSteps_zero (k : ℕ) (hk : 0 < k)
    (dt : RealB k) (f : RealB k → RealB k) (x : RealB k) :
    eulerSteps k hk dt f 0 x = x := by
  rfl

@[simp] theorem eulerSteps_succ (k : ℕ) (hk : 0 < k)
    (dt : RealB k) (f : RealB k → RealB k) (n : ℕ) (x : RealB k) :
    eulerSteps k hk dt f (n + 1) x =
      eulerSteps k hk dt f n (eulerStep k hk dt f x) := by
  rfl

@[simp] theorem eulerShadow_zero (k : ℕ) (hk : 0 < k)
    (dt : RealB k) (f : RealB k → RealB k) (x : RealB k) :
    eulerShadow k hk dt f 0 x = RealB.toRat hk x := by
  rfl

@[simp] theorem eulerShadow_succ (k : ℕ) (hk : 0 < k)
    (dt : RealB k) (f : RealB k → RealB k) (n : ℕ) (x : RealB k) :
    eulerShadow k hk dt f (n + 1) x =
      eulerShadow k hk dt f n x +
        RealB.toRat hk dt * RealB.toRat hk (f (eulerSteps k hk dt f n x)) := by
  rfl

theorem eulerSteps_succ_eq_step (k : ℕ) (hk : 0 < k)
    (dt : RealB k) (f : RealB k → RealB k) (n : ℕ) (x : RealB k) :
    eulerSteps k hk dt f (n + 1) x = eulerStep k hk dt f (eulerSteps k hk dt f n x) := by
  induction n generalizing x with
  | zero =>
      rfl
  | succ n ih =>
      simpa [eulerSteps] using ih (eulerStep k hk dt f x)

theorem eulerSteps_zero_dt (k : ℕ) (hk : 0 < k)
    (f : RealB k → RealB k) (n : ℕ) (x : RealB k) :
    eulerSteps k hk (RealB.default k) f n x = x := by
  induction n generalizing x with
  | zero =>
      rfl
  | succ n ih =>
      simp [eulerSteps, ih]

theorem eulerSteps_zero_field (k : ℕ) (hk : 0 < k)
    (dt : RealB k) (n : ℕ) (x : RealB k) :
    eulerSteps k hk dt (fun _ => RealB.default k) n x = x := by
  induction n generalizing x with
  | zero =>
      rfl
  | succ n ih =>
      simp [eulerSteps, ih]

@[simp] theorem eulerShadow_zero_dt (k : ℕ) (hk : 0 < k)
    (f : RealB k → RealB k) (n : ℕ) (x : RealB k) :
    eulerShadow k hk (RealB.default k) f n x = RealB.toRat hk x := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [eulerShadow, ih]

theorem eulerStep_shadow_error_le_two_halfSteps_of_abs_le_one (k : ℕ) (hk : 0 < k)
    (dt : RealB k) (f : RealB k → RealB k) (x : RealB k)
    (hmul : |RealB.toRat hk dt * RealB.toRat hk (f x)| ≤ 1)
    (hadd :
      |RealB.toRat hk x + RealB.toRat hk (RealB.mul hk dt (f x))| ≤ 1) :
    |RealB.toRat hk (eulerStep k hk dt f x) -
        (RealB.toRat hk x + RealB.toRat hk dt * RealB.toRat hk (f x))| ≤
      (2 : Rat) * RealB.halfStep k := by
  let drift := RealB.mul hk dt (f x)
  have houter :
      |RealB.toRat hk (eulerStep k hk dt f x) - (RealB.toRat hk x + RealB.toRat hk drift)| ≤
        RealB.halfStep k := by
    simpa [eulerStep, drift] using RealB.add_error_le_halfStep_of_abs_le_one hk x drift hadd
  have hinner :
      |RealB.toRat hk drift - (RealB.toRat hk dt * RealB.toRat hk (f x))| ≤
        RealB.halfStep k := by
    simpa [drift] using RealB.mul_error_le_halfStep_of_abs_le_one hk dt (f x) hmul
  have hsplit :
      RealB.toRat hk (eulerStep k hk dt f x) -
          (RealB.toRat hk x + RealB.toRat hk dt * RealB.toRat hk (f x)) =
        (RealB.toRat hk (eulerStep k hk dt f x) - (RealB.toRat hk x + RealB.toRat hk drift)) +
        (RealB.toRat hk drift - (RealB.toRat hk dt * RealB.toRat hk (f x))) := by
    dsimp [drift]
    ring
  rw [hsplit]
  calc
    _ ≤
        |RealB.toRat hk (eulerStep k hk dt f x) - (RealB.toRat hk x + RealB.toRat hk drift)| +
          |RealB.toRat hk drift - (RealB.toRat hk dt * RealB.toRat hk (f x))| := by
        exact abs_add_le _ _
    _ ≤ RealB.halfStep k + RealB.halfStep k := by
        gcongr
    _ = (2 : Rat) * RealB.halfStep k := by ring

theorem eulerSteps_shadow_error_le (k : ℕ) (hk : 0 < k)
    (dt : RealB k) (f : RealB k → RealB k) (n : ℕ) (x0 : RealB k)
    (hmul :
      ∀ m, |RealB.toRat hk dt * RealB.toRat hk (f (eulerSteps k hk dt f m x0))| ≤ 1)
    (hadd :
      ∀ m,
        |RealB.toRat hk (eulerSteps k hk dt f m x0) +
            RealB.toRat hk (RealB.mul hk dt (f (eulerSteps k hk dt f m x0)))| ≤ 1) :
    |RealB.toRat hk (eulerSteps k hk dt f n x0) - eulerShadow k hk dt f n x0| ≤
      ((2 * n : ℕ) : Rat) * RealB.halfStep k := by
  induction n with
  | zero =>
      simp [eulerShadow]
  | succ n ih =>
      let xn := eulerSteps k hk dt f n x0
      have hstep :
          |RealB.toRat hk (eulerStep k hk dt f xn) -
              (RealB.toRat hk xn + RealB.toRat hk dt * RealB.toRat hk (f xn))| ≤
            (2 : Rat) * RealB.halfStep k :=
        eulerStep_shadow_error_le_two_halfSteps_of_abs_le_one k hk dt f xn (hmul n) (hadd n)
      have hsplit :
          RealB.toRat hk (eulerSteps k hk dt f (n + 1) x0) - eulerShadow k hk dt f (n + 1) x0 =
            (RealB.toRat hk (eulerStep k hk dt f xn) -
                (RealB.toRat hk xn + RealB.toRat hk dt * RealB.toRat hk (f xn))) +
              (RealB.toRat hk xn - eulerShadow k hk dt f n x0) := by
        have hstep_eq : eulerSteps k hk dt f (n + 1) x0 = eulerStep k hk dt f xn := by
          simpa [xn] using eulerSteps_succ_eq_step k hk dt f n x0
        have hshadow_eq :
            eulerShadow k hk dt f (n + 1) x0 =
              eulerShadow k hk dt f n x0 + RealB.toRat hk dt * RealB.toRat hk (f xn) := by
          simp [eulerShadow, xn]
        rw [hstep_eq, hshadow_eq]
        ring_nf
      rw [hsplit]
      calc
        _ ≤
            |RealB.toRat hk (eulerStep k hk dt f xn) -
                (RealB.toRat hk xn + RealB.toRat hk dt * RealB.toRat hk (f xn))| +
              |RealB.toRat hk xn - eulerShadow k hk dt f n x0| := by
            exact abs_add_le _ _
        _ ≤ (2 : Rat) * RealB.halfStep k + (((2 * n : ℕ) : Rat) * RealB.halfStep k) := by
            gcongr
        _ = (((2 * (n + 1) : ℕ) : Rat) * RealB.halfStep k) := by
            norm_num
            ring

end HeytingLean.BST.Analysis
