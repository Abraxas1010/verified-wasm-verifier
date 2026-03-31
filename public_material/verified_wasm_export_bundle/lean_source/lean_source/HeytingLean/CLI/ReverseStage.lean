import Lean
import HeytingLean.CLI.SKYStageCore

/-!
# ReverseStage — Phase 4c of ProofBreeder Interactive Construction

Inverse of `stageExpr`/`stageLevel` in SKYStageCore: reconstruct `Lean.Expr`
from a staged `SExpr` using an inverse name table (`Nat → Name`).

This is mechanically invertible: each `SExpr` constructor maps 1:1 to a
`Lean.Expr` constructor. Erased universe params/mvars get placeholder names.

Trust chain:
- `Term.ofComb` (verified bridge) establishes that a Comb IS a valid decompilation
- `unstageExpr` (this module) reconstructs the `Lean.Expr` from the staged form
- Lean's kernel type check is the final authority
-/

open Lean

namespace HeytingLean.CLI.ReverseStage

open HeytingLean.CLI.SKYStageCore
open HeytingLean.LoF.LeanKernel

/-- Inverse name table: Nat → Name. -/
abbrev InverseNameTable := Std.HashMap Nat Name

/-- Build an InverseNameTable from an InternState. -/
def invertInternState (st : InternState) : InverseNameTable :=
  st.names.fold (init := {}) fun acc name id => acc.insert id name

/-- Inverse of stageLevel: SLevel → Lean.Level.
    Erased params/mvars get placeholder names. -/
def unstageLevel : SLevel → Lean.Level
  | .zero => .zero
  | .succ u => .succ (unstageLevel u)
  | .max a b => .max (unstageLevel a) (unstageLevel b)
  | .imax a b => .imax (unstageLevel a) (unstageLevel b)
  | .param () => .param `u
  | .mvar () => .mvar ⟨`m⟩

/-- Inverse of binderInfoToStaged. -/
def binderInfoFromStaged : HeytingLean.LoF.LeanKernel.BinderInfo → Lean.BinderInfo
  | .default => .default
  | .implicit => .implicit
  | .strictImplicit => .strictImplicit
  | .instImplicit => .instImplicit

/-- Inverse of stageExpr: SExpr → Lean.Expr using inverse name table.
    Returns `Except String` for unknown intern IDs. -/
partial def unstageExpr (nameTable : InverseNameTable) : SExpr → Except String Lean.Expr
  | .bvar idx => .ok (.bvar idx)
  | .mvar () => .ok (.mvar ⟨`placeholder⟩)
  | .sort u => .ok (.sort (unstageLevel u))
  | .const id us =>
      match nameTable.get? id with
      | some name => .ok (.const name (us.map unstageLevel))
      | none => .error s!"unknown intern id {id} in const"
  | .app f a => do
      let fe ← unstageExpr nameTable f
      let ae ← unstageExpr nameTable a
      .ok (.app fe ae)
  | .lam n bi ty body => do
      let name := nameTable.get? n |>.getD .anonymous
      let tye ← unstageExpr nameTable ty
      let bodye ← unstageExpr nameTable body
      .ok (.lam name tye bodye (binderInfoFromStaged bi))
  | .forallE n bi ty body => do
      let name := nameTable.get? n |>.getD .anonymous
      let tye ← unstageExpr nameTable ty
      let bodye ← unstageExpr nameTable body
      .ok (.forallE name tye bodye (binderInfoFromStaged bi))
  | .letE n _bi ty val body => do
      let name := nameTable.get? n |>.getD .anonymous
      let tye ← unstageExpr nameTable ty
      let vale ← unstageExpr nameTable val
      let bodye ← unstageExpr nameTable body
      .ok (.letE name tye vale bodye false)
  | .lit (.natVal n) => .ok (.lit (.natVal n))
  | .lit (.strVal s) => .ok (.lit (.strVal s))

/-- Roundtrip test: Lean.Expr → stageExpr → SExpr → unstageExpr → Lean.Expr.
    Returns the reconstructed expression or an error. -/
def stageUnstageRoundtrip (e : Lean.Expr) : Except String Lean.Expr := do
  match stageExprWithState {} e with
  | .error err => throw s!"staging failed: {err}"
  | .ok (staged, st) =>
      let invTable := invertInternState st
      unstageExpr invTable staged

end HeytingLean.CLI.ReverseStage
