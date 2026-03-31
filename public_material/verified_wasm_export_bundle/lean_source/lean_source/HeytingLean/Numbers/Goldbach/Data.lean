import Lean.Data.Json
import HeytingLean.Numbers.Goldbach.Core

/-
# Goldbach verification logs (JSON)

This module provides a small, semantics-level wrapper around the
JSON logs emitted by `tools/goldbach/verify.py`.

* The Python tool performs a bounded, deterministic search for
  Goldbach pairs up to a finite `N`.
* The resulting log is treated inside Lean as *data*: we parse the
  JSON into a structured type and expose predicates describing when
  the log witnesses `strongGoldbachUpTo N`.

No global Goldbach theorems are asserted here.  All statements are
local to the finite bound appearing in the log.
-/

namespace HeytingLean
namespace Numbers
namespace Goldbach

open Lean
open Lean.Json

namespace Verify

/-- A single Goldbach pair `(p, q)` as it appears in a verification log. -/
abbrev Pair := Nat × Nat

/-- An entry for a specific even `n`, together with the list of
candidate Goldbach pairs recorded for `n`. -/
structure EvenEntry where
  n     : Nat
  pairs : List Pair
  deriving Repr

/-- A bounded Goldbach verification log corresponding to the JSON
format `GoldbachVerify.v1` emitted by `tools/goldbach/verify.py`. -/
structure Log where
  version        : String
  N              : Nat
  evens          : List EvenEntry
  counterexamples : List Nat
  deriving Repr

namespace Internal

private def orErr {α} : Option α → String → Except String α
  | some a, _ => .ok a
  | none, msg => .error msg

/-- Parse a JSON array `[p, q]` into a Goldbach `Pair`. -/
def pairFromJson (j : Json) : Except String Pair := do
  let arr ←
    match j.getArr? with
    | .ok a => pure a
    | .error _ => .error "expected array for pair"
  match arr.toList with
  | jp :: jq :: [] =>
      let p ←
        match jp.getNat? with
        | .ok n => pure n
        | .error _ => .error "field 'p' not a Nat"
      let q ←
        match jq.getNat? with
        | .ok n => pure n
        | .error _ => .error "field 'q' not a Nat"
      pure (p, q)
  | _ => .error "expected array [p, q] for pair"

private def pairsFromJsonArray (arr : Array Json) :
    Except String (List Pair) :=
  let rec go (xs : List Json) : Except String (List Pair) := do
    match xs with
    | [] => pure []
    | j :: js =>
        let p ← pairFromJson j
        let rest ← go js
        pure (p :: rest)
  go arr.toList

/-- Parse a single even-entry object `{ "n": ..., "pairs": [...] }`. -/
def evenEntryFromJson (j : Json) : Except String EvenEntry := do
  let obj ←
    match j.getObj? with
    | .ok o => pure o
    | .error _ => .error "expected object for even entry"
  let nJ ← orErr (obj.get? "n") "missing field 'n'"
  let n ←
    match nJ.getNat? with
    | .ok v => pure v
    | .error _ => .error "field 'n' not a Nat"
  let pairsJ ← orErr (obj.get? "pairs") "missing field 'pairs'"
  let pairsArr ←
    match pairsJ.getArr? with
    | .ok a => pure a
    | .error _ => .error "field 'pairs' not an array"
  let pairs ← pairsFromJsonArray pairsArr
  pure { n, pairs }

private def evensFromJsonArray (arr : Array Json) :
    Except String (List EvenEntry) :=
  let rec go (xs : List Json) : Except String (List EvenEntry) := do
    match xs with
    | [] => pure []
    | j :: js =>
        let e ← evenEntryFromJson j
        let rest ← go js
        pure (e :: rest)
  go arr.toList

private def natListFromJsonArray (arr : Array Json) :
    Except String (List Nat) :=
  let rec go (xs : List Json) : Except String (List Nat) := do
    match xs with
    | [] => pure []
    | j :: js =>
        let n ←
          match j.getNat? with
          | .ok v => pure v
          | .error _ => .error "expected Nat in counterexamples array"
        let rest ← go js
        pure (n :: rest)
  go arr.toList

end Internal

/-- Parse a `GoldbachVerify.v1` JSON object into a `Log`. -/
def fromJsonE (j : Json) : Except String Log := do
  let obj ←
    match j.getObj? with
    | .ok o => pure o
    | .error _ => .error "expected object for Goldbach verify log"
  let vJ ← Internal.orErr (obj.get? "version") "missing field 'version'"
  let version ←
    match vJ.getStr? with
    | .ok s => pure s
    | .error _ => .error "field 'version' not a String"
  if version ≠ "GoldbachVerify.v1" then
    .error s!"unexpected version '{version}'"
  let nJ ← Internal.orErr (obj.get? "N") "missing field 'N'"
  let N ←
    match nJ.getNat? with
    | .ok v => pure v
    | .error _ => .error "field 'N' not a Nat"
  let evensJ ← Internal.orErr (obj.get? "evens") "missing field 'evens'"
  let evensArr ←
    match evensJ.getArr? with
    | .ok a => pure a
    | .error _ => .error "field 'evens' not an array"
  let evens ← Internal.evensFromJsonArray evensArr
  let counterJ ← Internal.orErr (obj.get? "counterexamples") "missing field 'counterexamples'"
  let counterArr ←
    match counterJ.getArr? with
    | .ok a => pure a
    | .error _ => .error "field 'counterexamples' not an array"
  let counterexamples ← Internal.natListFromJsonArray counterArr
  pure { version, N, evens, counterexamples }

/-- A log has a *witness* for an even `n` if it records at least one
candidate pair `(p, q)` for that `n` which satisfies the core
`isGoldbachPair` predicate. -/
def hasWitnessFor (log : Log) (n : Nat) : Prop :=
  ∃ e ∈ log.evens,
    e.n = n ∧
      ∃ pq ∈ e.pairs,
        isGoldbachPair n pq.1 pq.2

/-- The log witnesses the bounded strong Goldbach property up to `N`
if every even `n` with `4 ≤ n ≤ N` has at least one recorded
Goldbach pair.  This is a *semantic* property of the already-parsed
log; it does not claim any global theorem beyond the bound. -/
def logWitnessesStrongUpTo (log : Log) (N : Nat) : Prop :=
  N ≤ log.N ∧
    ∀ n : Nat, 4 ≤ n ∧ n ≤ N ∧ Even n →
      hasWitnessFor log n

end Verify

/-- If a verification log witnesses the strong Goldbach property up to
`N`, then (assuming the log's Goldbach pairs are correct) this
implies the `strongGoldbachUpTo N` predicate from `Core`.  This lemma
is deliberately *conditional* on the `logWitnessesStrongUpTo` assumption
and does not assume any correctness of the external computation
by itself. -/
theorem strongGoldbachUpTo_of_logWitnesses
    {log : Verify.Log} {N : Nat}
    (h : Verify.logWitnessesStrongUpTo log N) :
    strongGoldbachUpTo N := by
  intro n hn
  rcases hn with ⟨h4, hEven, hLe⟩
  have hN : N ≤ log.N := h.left
  have hWitness :=
    h.right n ⟨h4, hLe, hEven⟩
  rcases hWitness with ⟨e, heIn, heEq, pq, hpqIn, hPair⟩
  exact ⟨pq.1, pq.2, hPair⟩

end Goldbach
end Numbers
end HeytingLean
