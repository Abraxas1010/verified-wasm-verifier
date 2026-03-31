import HeytingLean.Constructor.CT.TaskExistence

/-!
# Multi-round task combinators (syntax + possibility lifting)

This module provides a minimal “multi-round” surface for CT tasks:

- syntactic iteration of `Task.seq` and `Task.par`;
- possibility lifting lemmas for `TaskCT` (constructor-existence semantics).

Important: CT’s core interface only gives *forward* closure
(`possible T` and `possible U` imply `possible (T;U)` / `possible (T ⊗ U)`).
We therefore do **not** prove any “projection” lemmas from a composite task back
to its components here.
-/

namespace HeytingLean
namespace Constructor
namespace CT

universe u

namespace Task

variable {σ : Type u}

/-- A syntactic “repeat `seq`” combinator.

`seqPow 0 T = []` (empty task), and `seqPow (n+1) T = (seqPow n T);T`.
-/
def seqPow (n : ℕ) (T : Task σ) : Task σ :=
  Nat.rec (motive := fun _ => Task σ) { arcs := [] }
    (fun _ acc => Task.seq acc T) n

/-- A syntactic “repeat `par`” combinator.

`parPow 0 T = []` (empty task), and `parPow (n+1) T = (parPow n T) ⊗ T`.
-/
def parPow (n : ℕ) (T : Task σ) : Task σ :=
  Nat.rec (motive := fun _ => Task σ) { arcs := [] }
    (fun _ acc => Task.par acc T) n

@[simp] theorem seqPow_zero (T : Task σ) : (seqPow 0 T).arcs = [] := rfl
@[simp] theorem parPow_zero (T : Task σ) : (parPow 0 T).arcs = [] := rfl

@[simp] theorem seqPow_succ (n : ℕ) (T : Task σ) :
    seqPow (n + 1) T = Task.seq (seqPow n T) T := by
  rfl

@[simp] theorem parPow_succ (n : ℕ) (T : Task σ) :
    parPow (n + 1) T = Task.par (parPow n T) T := by
  rfl

end Task

namespace TaskCT

variable {σ : Type u} (CT : TaskCT σ)

/-- If `T` is possible, then `seqPow (n+1) T` is possible (multi-round serial repetition). -/
theorem possible_seqPow_succ {n : ℕ} {T : Task σ} :
    CT.possible T → CT.possible (Task.seqPow (n + 1) T) := by
  intro hT
  induction n with
  | zero =>
    simpa [Task.seqPow, Nat.rec] using hT
  | succ n ih =>
    -- `seqPow (n+2) T = (seqPow (n+1) T);T`.
    have hPrev : CT.possible (Task.seqPow (n + 1) T) := ih
    have : CT.possible (Task.seq (Task.seqPow (n + 1) T) T) :=
      CT.possible_seq hPrev hT
    simpa [Task.seqPow, Nat.rec, Nat.succ_eq_add_one, Nat.add_assoc] using this

/-- If `T` is possible, then `parPow (n+1) T` is possible (multi-round parallel repetition). -/
theorem possible_parPow_succ {n : ℕ} {T : Task σ} :
    CT.possible T → CT.possible (Task.parPow (n + 1) T) := by
  intro hT
  induction n with
  | zero =>
    simpa [Task.parPow, Nat.rec] using hT
  | succ n ih =>
    have hPrev : CT.possible (Task.parPow (n + 1) T) := ih
    have : CT.possible (Task.par (Task.parPow (n + 1) T) T) :=
      CT.possible_par hPrev hT
    simpa [Task.parPow, Nat.rec, Nat.succ_eq_add_one, Nat.add_assoc] using this

end TaskCT

end CT
end Constructor
end HeytingLean
