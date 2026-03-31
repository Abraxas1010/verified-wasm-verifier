import Lean
import HeytingLean.Theorems.Core

namespace HeytingLean.Exec

open Lean
open HeytingLean.Theorems

/-- Arity marker for executable processes. -/
inductive Arity
| unary
| binary
  deriving Repr, DecidableEq, BEq

/-- Render an arity as a human-readable string. -/
def arityToString : Arity → String
| .unary  => "unary"
| .binary => "binary"

/-- Abstract computation state, modeled as a JSON payload. -/
structure State where
  payload : Json
  deriving BEq

/-- Specification for a process: which theorem justifies it, and optional notes. -/
structure ProcSpec where
  specThm : ThmId
  notes   : Option String := none
  deriving Repr

/-- A process is an identified state transformer with a spec. -/
structure Proc where
  id   : String
  arity : Arity
  spec : ProcSpec
  run  : State → IO State

namespace State

/-- Structural equality on states via JSON equality. -/
def eq (s₁ s₂ : State) : Bool :=
  s₁.payload == s₂.payload

end State

/-- Run a process until it reaches a fixed point (state equality). -/
def runToFixedPoint (p : Proc) (s₀ : State) (maxSteps : Nat := 1024) : IO (State × Bool) := do
  let rec loop (fuel : Nat) (s : State) : IO (State × Bool) := do
    match fuel with
    | 0 => pure (s, false)
    | Nat.succ k =>
        let s' ← p.run s
        if s'.payload == s.payload then
          pure (s', true)
        else
          loop k s'
  loop maxSteps s₀

/-- Internal helper: convert a JSON number to `Nat` if possible. -/
private def numToNat? (n : JsonNumber) : Option Nat :=
  n.toString.toNat?

/-- Safe array lookup helper. -/
private def arrayGet? {α} (a : Array α) (i : Nat) : Option α :=
  let rec loop : List α → Nat → Option α
    | [], _ => none
    | x :: _, 0 => some x
    | _ :: xs, Nat.succ n => loop xs n
  loop a.toList i

/-- Expect an array-valued `args` field inside the state payload. -/
private def expectArgs (s : State) : Except String (Array Json) :=
  match s.payload with
  | Json.obj _ =>
      match s.payload.getObjVal? "args" with
      | Except.ok (Json.arr a) => Except.ok a
      | _ => Except.error "expected field 'args' as a JSON array"
  | _ =>
      Except.error "expected object payload with 'args' array"

/-- Try to decode a single `Nat` argument from a state payload. -/
def decodeUnaryArgs (s : State) : Except String Nat := do
  let args ← expectArgs s
  match arrayGet? args 0 with
  | some (Json.num n) =>
      match numToNat? n with
      | some v => Except.ok v
      | none => Except.error "expected args[0] to be a Nat"
  | _ => Except.error "expected args[0] to be a number"

/-- Try to decode two `Nat` arguments from a state payload. -/
def decodeBinaryArgs (s : State) : Except String (Nat × Nat) := do
  let args ← expectArgs s
  let fetch (idx : Nat) : Except String Nat := do
    match arrayGet? args idx with
    | some (Json.num n) =>
        match numToNat? n with
        | some v => Except.ok v
        | none => Except.error s!"expected args[{idx}] to be a Nat"
    | _ => Except.error s!"expected args[{idx}] to be a number"
  return (← fetch 0, ← fetch 1)

end HeytingLean.Exec
