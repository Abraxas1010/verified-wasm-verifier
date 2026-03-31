import Mathlib.Data.Finset.Basic
import HeytingLean.Crypto.Form
import HeytingLean.Crypto.BoolLens

/-!
# Prepaid-Escrow Guard (PEG v0)

Lean-side scaffold for a per-step guard encoded as a Boolean `Form 5`.
This module exposes:
  - `Step`: host-side observables for one step (types are minimal stand-ins).
  - `envOf`: adapter from `Step` to the Boolean environment expected by `Form 5`.
  - `permitForm`: x0 ∧ x1 ∧ x3 ∧ x4 over Fin 5 variables.
  - `permitted`: native Bool-lens evaluation for quick checks.

It integrates with the existing ML-ZKPCT pipeline (BoolLens → VM → R1CS) via
the general theorems in `HeytingLean.Crypto.ZK.R1CSSoundness` and the CLIs.
-/

namespace HeytingLean
namespace Blockchain
namespace Contracts

structure Step where
  toAddr      : Nat
  vendor      : Nat
  spentNow    : Nat
  unitPrice   : Nat
  agreedPrice : Nat
  budget      : Nat
  fnId        : UInt32
  whitelist   : Finset UInt32
  now         : Nat
  startTs     : Nat
  endTs       : Nat
  deriving Inhabited

namespace PEGv0

open HeytingLean.Crypto

abbrev Env5 := BoolLens.Env 5

/-- Map a `Step` into the five Boolean atoms expected by the PEG v0 form. -/
def envOf (s : Step) : Env5 :=
  fun i =>
    match i.val with
    | 0 => decide (s.toAddr = s.vendor)
    | 1 => decide (s.spentNow + s.unitPrice ≤ s.budget)
    | 2 => decide (s.unitPrice = s.agreedPrice)
    | 3 => decide (s.fnId ∈ s.whitelist)
    | 4 => decide (s.startTs ≤ s.now ∧ s.now ≤ s.endTs)
    | _ => false

/-- x0 ∧ x1 ∧ x3 ∧ x4 over `Fin 5`. -/
def permitForm : Form 5 :=
  Form.and (Form.var ⟨0, by decide⟩)
          (Form.and (Form.var ⟨1, by decide⟩)
                     (Form.and (Form.var ⟨3, by decide⟩)
                                (Form.var ⟨4, by decide⟩)))

/-- Native Bool-lens decision (fast local check). -/
def permitted (s : Step) : Bool :=
  BoolLens.eval permitForm (envOf s)

end PEGv0
end Contracts
end Blockchain
end HeytingLean
