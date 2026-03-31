import HeytingLean.PerspectivalPlenum.DirectConnection

namespace HeytingLean
namespace PerspectivalPlenum

universe u

/-- Compatibility witness required before composing ratchet steps. -/
structure RatchetCompatibility {α : Type u} [Order.Frame α]
    (S T : RatchetStep α) : Prop where
  commute : ∀ J : Nucleus α, S (T J) = T (S J)

namespace RatchetStep

variable {α : Type u} [Order.Frame α]

/-- Iterate a ratchet step over a base nucleus. -/
def iterate (S : RatchetStep α) : Nat → Nucleus α → Nucleus α
  | 0, J => J
  | Nat.succ n, J => S (iterate S n J)

@[simp] theorem iterate_zero (S : RatchetStep α) (J : Nucleus α) :
    iterate S 0 J = J := rfl

@[simp] theorem iterate_succ (S : RatchetStep α) (n : Nat) (J : Nucleus α) :
    iterate S (Nat.succ n) J = S (iterate S n J) := by
  simp [iterate]

/-- Every iterate remains above the base nucleus by extensivity. -/
theorem le_iterate (S : RatchetStep α) (J : Nucleus α) :
    ∀ n : Nat, J ≤ iterate S n J
  | 0 => le_rfl
  | Nat.succ n =>
      le_trans (le_iterate (S := S) (J := J) n) (S.extensive (iterate S n J))

/-- Iterate is monotone in its base nucleus for each fixed depth. -/
theorem iterate_monotone (S : RatchetStep α) (n : Nat) :
    Monotone (iterate S n) := by
  induction n with
  | zero =>
      intro J K hJK
      exact hJK
  | succ n ih =>
      intro J K hJK
      exact S.monotone (ih hJK)

@[simp] theorem iterate_one (S : RatchetStep α) (J : Nucleus α) :
    iterate S 1 J = S J := by
  simp [iterate]

@[simp] theorem iterate_two_eq_one (S : RatchetStep α) (J : Nucleus α) :
    iterate S 2 J = iterate S 1 J := by
  simp [iterate, S.step_step]

/-- Once at least one ratchet step has been applied, the tower stabilizes. -/
theorem iterate_succ_eq_one (S : RatchetStep α) (J : Nucleus α) :
    ∀ n : Nat, iterate S (Nat.succ n) J = iterate S 1 J
  | 0 => by simp [iterate]
  | Nat.succ n => by
      calc
        iterate S (Nat.succ (Nat.succ n)) J
            = S (iterate S (Nat.succ n) J) := by simp [iterate]
        _ = S (iterate S 1 J) := by
          rw [iterate_succ_eq_one (S := S) (J := J) n]
        _ = iterate S 1 J := by
          simp [iterate, S.step_step]

/-- Applying one more ratchet step after stage 1 is idempotence-safe. -/
theorem iterate_idempotence_safe (S : RatchetStep α) (J : Nucleus α) (n : Nat) :
    S (iterate S (Nat.succ n) J) = iterate S (Nat.succ n) J := by
  rw [iterate_succ_eq_one (S := S) (J := J) (n := n)]
  simp [iterate]

/-- Guarded composition of ratchet steps, available only under explicit commutation. -/
def compose (S T : RatchetStep α) (h : RatchetCompatibility S T) : RatchetStep α where
  step J := S (T J)
  extensive J := le_trans (T.extensive J) (S.extensive (T J))
  monotone := S.monotone.comp T.monotone
  idempotent J := by
    calc
      S (T (S (T J))) = T (S (S (T J))) := by
        simpa using h.commute (S (T J))
      _ = T (S (T J)) := by simp [S.step_step]
      _ = S (T (T J)) := by
        simpa using (h.commute (T J)).symm
      _ = S (T J) := by simp [T.step_step]

@[simp] theorem compose_apply (S T : RatchetStep α) (h : RatchetCompatibility S T)
    (J : Nucleus α) :
    compose S T h J = S (T J) := rfl

end RatchetStep

/-- A finite re-re-entry tower: base nucleus plus ratchet step. -/
structure RatchetTower (α : Type u) [Order.Frame α] where
  base : Nucleus α
  step : RatchetStep α

namespace RatchetTower

variable {α : Type u} [Order.Frame α]

/-- Layer `n` in the re-re-entry tower. -/
def layer (T : RatchetTower α) (n : Nat) : Nucleus α :=
  RatchetStep.iterate T.step n T.base

@[simp] theorem layer_zero (T : RatchetTower α) :
    T.layer 0 = T.base := rfl

@[simp] theorem layer_one (T : RatchetTower α) :
    T.layer 1 = T.step T.base := by
  simp [layer, RatchetStep.iterate]

@[simp] theorem layer_succ (T : RatchetTower α) (n : Nat) :
    T.layer (Nat.succ n) = T.step (T.layer n) := by
  simp [layer, RatchetStep.iterate]

/-- Base nucleus embeds into every layer. -/
theorem base_le_layer (T : RatchetTower α) (n : Nat) :
    T.base ≤ T.layer n :=
  RatchetStep.le_iterate T.step T.base n

/-- The tower stabilizes after the first nontrivial layer. -/
theorem layer_stabilizes (T : RatchetTower α) (n : Nat) :
    T.layer (Nat.succ n) = T.layer 1 :=
  RatchetStep.iterate_succ_eq_one T.step T.base n

/-- Stratification by applying a finite list of ratchet steps in sequence. -/
def stratify (base : Nucleus α) (steps : List (RatchetStep α)) : Nucleus α :=
  steps.foldl (fun J S => S J) base

@[simp] theorem stratify_nil (base : Nucleus α) :
    stratify base [] = base := rfl

@[simp] theorem stratify_cons (base : Nucleus α)
    (S : RatchetStep α) (rest : List (RatchetStep α)) :
    stratify base (S :: rest) = stratify (S base) rest := rfl

/-- Stratification is extensive over the initial base nucleus. -/
theorem base_le_stratify (base : Nucleus α) (steps : List (RatchetStep α)) :
    base ≤ stratify base steps := by
  induction steps generalizing base with
  | nil =>
      simp [stratify]
  | cons S rest ih =>
      exact le_trans (S.extensive base) (by simpa [stratify] using ih (S base))

/-- Adjacent duplicate steps collapse by idempotence. -/
@[simp] theorem stratify_duplicate_head (base : Nucleus α)
    (S : RatchetStep α) (rest : List (RatchetStep α)) :
    stratify base (S :: S :: rest) = stratify base (S :: rest) := by
  simp [stratify, S.step_step]

end RatchetTower

end PerspectivalPlenum
end HeytingLean
