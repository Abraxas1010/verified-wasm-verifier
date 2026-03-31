import HeytingLean.LoF.Combinators.SKY

/-!
# SKY eigenform demo CLI (Kauffman Phase 5, core)

This executable exercises the SKY combinator layer's fixed-point primitive `Y`:

* `Y f` reduces to `f (Y f)`;
* in particular, `Y (K t)` reduces to `t`, exhibiting a concrete eigenform.

We implement a tiny fuel-limited reducer (leftmost-outermost) and run two checks:
* `I · t ↦* t` (sanity for the `S`/`K` rules),
* `Y (K S) ↦* S` (a fixed point for a constant function).
-/

namespace HeytingLean.CLI.SKYEigenformDemoMain

open HeytingLean.LoF

private def die (msg : String) : IO UInt32 := do
  IO.eprintln msg
  pure 1

private def ok (b : Bool) (msg : String) : IO Unit := do
  if !b then
    throw (IO.userError msg)

private def okEq {α} [DecidableEq α] (x y : α) (msg : String) : IO Unit :=
  ok (decide (x = y)) msg

/-- Deterministic one-step SKY reduction (leftmost-outermost). -/
private def step? : Comb → Option Comb
  | Comb.app (Comb.app Comb.K x) _ => some x
  | Comb.app (Comb.app (Comb.app Comb.S x) y) z =>
      some (Comb.app (Comb.app x z) (Comb.app y z))
  | Comb.app Comb.Y f =>
      some (Comb.app f (Comb.app Comb.Y f))
  | Comb.app f a =>
      match step? f with
      | some f' => some (Comb.app f' a)
      | none =>
          match step? a with
          | some a' => some (Comb.app f a')
          | none => none
  | _ => none

/-- Reduce for at most `fuel` steps, stopping early at normal forms. -/
private def reduceFuel : Nat → Comb → Comb
  | 0, t => t
  | Nat.succ n, t =>
      match step? t with
      | some t' => reduceFuel n t'
      | none => t

def main (_argv : List String) : IO UInt32 := do
  try
    let t : Comb := Comb.S
    let idOut := reduceFuel 8 (Comb.app Comb.I t)
    okEq idOut t s!"SKY identity check failed: got {reprStr idOut}"

    let yTerm : Comb := Comb.app Comb.Y (Comb.app Comb.K Comb.S)
    let yOut := reduceFuel 8 yTerm
    okEq yOut Comb.S s!"SKY Y eigenform failed: got {reprStr yOut}"

    IO.println "sky_eigenform_demo: ok"
    pure 0
  catch e =>
    die s!"sky_eigenform_demo: FAILED: {e}"

end HeytingLean.CLI.SKYEigenformDemoMain

open HeytingLean.CLI.SKYEigenformDemoMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.SKYEigenformDemoMain.main args

