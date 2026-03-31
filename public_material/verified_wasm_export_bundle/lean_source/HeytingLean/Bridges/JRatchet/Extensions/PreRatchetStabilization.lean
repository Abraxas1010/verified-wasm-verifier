import HeytingLean.Bridges.JRatchet.Extensions.PataraiaNuclearJoin

/-!
# PreRatchetStabilization

This module records a stabilization interface for pre-ratchet operators,
following the dcpo-closure perspective (Dacar 2021) at the second-order level.

Implementation note:
`stabilize` is realized by the join-reflection from
`PataraiaNuclearJoin.ratchetStepJoin`.
-/

namespace HeytingLean
namespace Bridges
namespace JRatchet
namespace Extensions
namespace PreRatchetStabilization

open HeytingLean.PerspectivalPlenum

universe u

variable {α : Type u} [Order.Frame α]

/-- Local abbreviation for pre-ratchet steps from the Pataraia join module. -/
abbrev PreRatchetStep (α : Type u) [Order.Frame α] :=
  PataraiaNuclearJoin.PreRatchetStep (α := α)

/-- Iteration of a pre-ratchet step on nuclei. -/
def iterate (P : PreRatchetStep α) : Nat → Nucleus α → Nucleus α
  | 0, J => J
  | Nat.succ n, J => P.step (iterate P n J)

/-- Zeroth iterate is the base nucleus. -/
@[simp] theorem iterate_zero (P : PreRatchetStep α) (J : Nucleus α) :
    iterate P 0 J = J := rfl

/-- Successor iterate applies one extra pre-ratchet step. -/
@[simp] theorem iterate_succ (P : PreRatchetStep α) (n : Nat) (J : Nucleus α) :
    iterate P (Nat.succ n) J = P.step (iterate P n J) := rfl

/-- Every iterate is above the base nucleus. -/
theorem le_iterate (P : PreRatchetStep α) (J : Nucleus α) :
    ∀ n : Nat, J ≤ iterate P n J
  | 0 => le_rfl
  | Nat.succ n =>
      le_trans (le_iterate P J n) (P.extensive (iterate P n J))

/-- Iteration is monotone in the base nucleus for each fixed depth. -/
theorem iterate_monotone (P : PreRatchetStep α) (n : Nat) :
    Monotone (iterate P n) := by
  induction n with
  | zero =>
      intro J K hJK
      simpa using hJK
  | succ n ih =>
      intro J K hJK
      exact P.monotone (ih hJK)

/-- Canonical fixed-point candidate from iterative completion.

In this implementation, this is definitionally the `ratchetStepJoin` image.
-/
noncomputable def iterateToFixed (P : PreRatchetStep α) (J : Nucleus α) : Nucleus α :=
  (PataraiaNuclearJoin.ratchetStepJoin P).step J

/-- Stabilization of a pre-ratchet step into a true ratchet step. -/
noncomputable def stabilize (P : PreRatchetStep α) : RatchetStep α :=
  PataraiaNuclearJoin.ratchetStepJoin P

/-- Stabilization is extensive on nuclei. -/
theorem stabilize_extensive (P : PreRatchetStep α) :
    ∀ J : Nucleus α, J ≤ (stabilize P).step J :=
  (stabilize P).extensive

/-- Stabilization is monotone on nuclei. -/
theorem stabilize_monotone (P : PreRatchetStep α) :
    Monotone (stabilize P).step :=
  (stabilize P).monotone

/-- Stabilization is idempotent on nuclei. -/
theorem stabilize_idempotent (P : PreRatchetStep α) :
    ∀ J : Nucleus α,
      (stabilize P).step ((stabilize P).step J) = (stabilize P).step J :=
  (stabilize P).idempotent

/-- Minimality of stabilization against nucleus-on-nuclei upper bounds. -/
theorem stabilize_le_of_dominates
    (P : PreRatchetStep α)
    {n : Nucleus (Nucleus α)}
    (hdom : ∀ J : Nucleus α, P.step J ≤ n J) :
    ∀ J : Nucleus α, (stabilize P).step J ≤ n J :=
  PataraiaNuclearJoin.ratchetStepJoin_leastNucleus P hdom

/-- Promote an idempotent pre-ratchet specification to a ratchet step. -/
def toRatchetStep
    (P : PreRatchetStep α)
    (hidem : ∀ J : Nucleus α, P.step (P.step J) = P.step J) : RatchetStep α where
  step := P.step
  extensive := P.extensive
  monotone := P.monotone
  idempotent := hidem

/-- If a pre-ratchet is already idempotent, stabilization preserves its upper-bound behavior. -/
theorem stabilize_of_idempotent
    (P : PreRatchetStep α)
    (hidem : ∀ J : Nucleus α, P.step (P.step J) = P.step J) :
    ∀ J : Nucleus α,
      (toRatchetStep P hidem).step J ≤ (stabilize P).step J :=
  PataraiaNuclearJoin.ratchetStepJoin_upper P

/--
Every finite iterate of a pre-ratchet step is bounded above by the stabilized ratchet value.

This theorem links the iteration lane (`iterate`) to the stabilized lane (`stabilize`).
-/
theorem iterate_le_stabilize (P : PreRatchetStep α) (J : Nucleus α) :
    ∀ n : Nat, iterate P n J ≤ (stabilize P).step J
  | 0 => stabilize_extensive P J
  | Nat.succ n => by
      have hUpper : P.step (iterate P n J) ≤ (stabilize P).step (iterate P n J) :=
        PataraiaNuclearJoin.ratchetStepJoin_upper P (iterate P n J)
      have hRec : iterate P n J ≤ (stabilize P).step J :=
        iterate_le_stabilize P J n
      have hMon :
          (stabilize P).step (iterate P n J) ≤
            (stabilize P).step ((stabilize P).step J) :=
        (stabilize_monotone P) hRec
      have hIdem : (stabilize P).step ((stabilize P).step J) = (stabilize P).step J :=
        stabilize_idempotent P J
      exact le_trans hUpper (by simpa [hIdem] using hMon)

end PreRatchetStabilization
end Extensions
end JRatchet
end Bridges
end HeytingLean
