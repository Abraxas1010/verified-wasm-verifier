import Mathlib.Order.MinMax
/-!
# IteratedVirtual.Bridge.ModalSketch

Strict-only: a small *syntax-level* modal-logic bridge piece, sufficient for:

- defining modal formulas,
- defining the Gödel-style “box everywhere” translation,
- tracking modal depth.

This module intentionally does **not** attempt to formalize S4 semantics or prove the
Gödel–McKinsey–Tarski correspondence theorem; that would require aligning with an existing modal
logic development (e.g. the `Foundation` dependency already in HeytingLean).
-/

namespace HeytingLean
namespace IteratedVirtual
namespace Bridge

inductive ModalFormula : Type
  | atom : String → ModalFormula
  | neg : ModalFormula → ModalFormula
  | conj : ModalFormula → ModalFormula → ModalFormula
  | disj : ModalFormula → ModalFormula → ModalFormula
  | impl : ModalFormula → ModalFormula → ModalFormula
  | box : ModalFormula → ModalFormula
  | diamond : ModalFormula → ModalFormula
deriving Repr, DecidableEq

notation "□" φ => ModalFormula.box φ
notation "◇" φ => ModalFormula.diamond φ

/-- Modal nesting depth (`□` and `◇` both count). -/
def modalDepth : ModalFormula → Nat
  | .atom _ => 0
  | .neg φ => modalDepth φ
  | .conj φ ψ => Nat.max (modalDepth φ) (modalDepth ψ)
  | .disj φ ψ => Nat.max (modalDepth φ) (modalDepth ψ)
  | .impl φ ψ => Nat.max (modalDepth φ) (modalDepth ψ)
  | .box φ => Nat.succ (modalDepth φ)
  | .diamond φ => Nat.succ (modalDepth φ)

/-- Gödel translation: prefix `□` at every node. -/
def goedelTranslation : ModalFormula → ModalFormula
  | .atom p => □(.atom p)
  | .neg φ => □(.neg (goedelTranslation φ))
  | .conj φ ψ => □(.conj (goedelTranslation φ) (goedelTranslation ψ))
  | .disj φ ψ => □(.disj (goedelTranslation φ) (goedelTranslation ψ))
  | .impl φ ψ => □(.impl (goedelTranslation φ) (goedelTranslation ψ))
  | .box φ => □(goedelTranslation φ)
  | .diamond φ => □(.diamond (goedelTranslation φ))

theorem modalDepth_goedelTranslation_pos (φ : ModalFormula) :
    0 < modalDepth (goedelTranslation φ) := by
  cases φ <;> simp [goedelTranslation, modalDepth]

theorem modalDepth_le_goedelTranslation (φ : ModalFormula) :
    modalDepth φ ≤ modalDepth (goedelTranslation φ) := by
  induction φ with
  | atom p =>
      simp [goedelTranslation, modalDepth]
  | neg φ ih =>
      -- `neg` does not increase depth; translation adds an outer `□`.
      simpa [goedelTranslation, modalDepth] using Nat.le_trans ih (Nat.le_succ _)
  | conj φ ψ ihφ ihψ =>
      have hmax : Nat.max (modalDepth φ) (modalDepth ψ) ≤
          Nat.max (modalDepth (goedelTranslation φ)) (modalDepth (goedelTranslation ψ)) :=
        max_le_max ihφ ihψ
      simpa [goedelTranslation, modalDepth] using Nat.le_trans hmax (Nat.le_succ _)
  | disj φ ψ ihφ ihψ =>
      have hmax : Nat.max (modalDepth φ) (modalDepth ψ) ≤
          Nat.max (modalDepth (goedelTranslation φ)) (modalDepth (goedelTranslation ψ)) :=
        max_le_max ihφ ihψ
      simpa [goedelTranslation, modalDepth] using Nat.le_trans hmax (Nat.le_succ _)
  | impl φ ψ ihφ ihψ =>
      have hmax : Nat.max (modalDepth φ) (modalDepth ψ) ≤
          Nat.max (modalDepth (goedelTranslation φ)) (modalDepth (goedelTranslation ψ)) :=
        max_le_max ihφ ihψ
      simpa [goedelTranslation, modalDepth] using Nat.le_trans hmax (Nat.le_succ _)
  | box φ ih =>
      -- Translation adds an extra `□` above the existing one.
      simpa [goedelTranslation, modalDepth] using Nat.succ_le_succ ih
  | diamond φ ih =>
      -- Translation wraps `◇` in an extra outer `□`, so we get an extra `+1` slack on the RHS.
      have h1 : Nat.succ (modalDepth φ) ≤ Nat.succ (modalDepth (goedelTranslation φ)) :=
        Nat.succ_le_succ ih
      -- `succ (d) ≤ succ (succ d)` for any `d`.
      have h2 : Nat.succ (modalDepth (goedelTranslation φ)) ≤ Nat.succ (Nat.succ (modalDepth (goedelTranslation φ))) :=
        Nat.le_succ _
      -- Put the pieces together.
      simpa [goedelTranslation, modalDepth] using Nat.le_trans h1 h2

end Bridge
end IteratedVirtual
end HeytingLean
