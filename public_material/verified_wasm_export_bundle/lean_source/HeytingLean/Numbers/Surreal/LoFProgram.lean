import HeytingLean.Numbers.SurrealCore
import Std

/-!
# Surreal LoF-style program DSL (mark / unmark / re-entry)

This module introduces a small, *flat* program representation for
finite surreal pre-games, inspired by Laws of Form primitives:

- **unmark**: the null cut `{∅ | ∅}` (base case)
- **mark**: the separator `{L | R}` (build a cut from options)
- **re-entry**: references to previously-defined nodes (indices)

The DSL is intentionally minimal and executable. It supports:

* evaluation to `SurrealCore.PreGame` with robust error reporting,
* optional birthday bounds during evaluation, and
* a compiler from `PreGame` into a well-formed program.

This is a *finite* story: birthdays are `Nat` and programs are
acyclic by construction (only backward references are permitted).
-/

namespace HeytingLean
namespace Numbers
namespace Surreal

open HeytingLean.Numbers.SurrealCore

namespace LoFProgram

/-- A flat instruction set for constructing pre-games. -/
inductive Op where
  | unmark
  | mark (L R : List Nat)
  deriving Repr, DecidableEq

/-- A program is a sequence of operations with a designated root node. -/
structure Program where
  ops : Array Op
  root : Nat
  deriving Repr, DecidableEq

namespace Program

def size (p : Program) : Nat := p.ops.size

def getOp? (p : Program) (i : Nat) : Option Op := p.ops[i]?

def isWellFormed (p : Program) : Bool :=
  Id.run do
    let mut ok := true
    for h : i in [:p.ops.size] do
      if !ok then
        break
      let op := p.ops[i]
      match op with
      | .unmark => pure ()
      | .mark L R =>
          for j in L do
            if !(j < i) then
              ok := false
          for j in R do
            if !(j < i) then
              ok := false
    if !(p.root < p.ops.size) then
      ok := false
    return ok

private def getNode? (env : Array PreGame) (idx : Nat) : Except String PreGame :=
  match env[idx]? with
  | some g => .ok g
  | none => .error s!"invalid re-entry index {idx} (env size={env.size})"

private def evalOp (env : Array PreGame) : Op → Except String PreGame
  | .unmark => .ok nullCut
  | .mark L R => do
      let mut Lg : List PreGame := []
      let mut Rg : List PreGame := []
      for j in L do
        let g ← getNode? env j
        Lg := g :: Lg
      for j in R do
        let g ← getNode? env j
        Rg := g :: Rg
      return PreGame.build Lg.reverse Rg.reverse

/-- Evaluate a program into the full array of computed nodes (one per op). -/
def evalAll (p : Program) : Except String (Array PreGame) := do
  if !p.isWellFormed then
    throw s!"program ill-formed (root or re-entry indices out of range)"
  let mut env : Array PreGame := #[]
  for h : i in [:p.ops.size] do
    let g ← evalOp env (p.ops[i])
    env := env.push g
  return env

/-- Evaluate a program to a pre-game (or an explanatory error). -/
def eval (p : Program) : Except String PreGame := do
  let env ← evalAll p
  getNode? env p.root

/-- Evaluate with an optional birthday bound; fails if any intermediate
node exceeds the bound. -/
def evalWithMaxBirth (p : Program) (θ : Nat) : Except String PreGame := do
  if !p.isWellFormed then
    throw s!"program ill-formed (root or re-entry indices out of range)"
  let mut env : Array PreGame := #[]
  for h : i in [:p.ops.size] do
    let g ← evalOp env (p.ops[i])
    if g.birth > θ then
      throw s!"birthday bound exceeded at op {i}: birth={g.birth} > θ={θ}"
    env := env.push g
  let root ← getNode? env p.root
  if root.birth > θ then
    throw s!"birthday bound exceeded at root: birth={root.birth} > θ={θ}"
  return root

end Program

/-! ## Normalisation and compilation -/

/-! ### Termination helpers -/

private theorem sizeOf_lt_sizeOf_list_of_mem [SizeOf α] {x : α} {xs : List α} (hx : x ∈ xs) :
    sizeOf x < sizeOf xs := by
  induction xs with
  | nil => cases hx
  | cons h t ih =>
      cases hx with
      | head =>
          have hpos : 0 < 1 + sizeOf t := by
            have : 0 < sizeOf t + 1 := Nat.succ_pos _
            simpa [Nat.add_comm] using this
          have hlt : sizeOf x < sizeOf x + (1 + sizeOf t) :=
            Nat.lt_add_of_pos_right hpos
          simpa [List.cons.sizeOf_spec, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlt
      | tail _ hx1 =>
          have hlt : sizeOf x < sizeOf t := ih hx1
          have htpos : 0 < 1 + sizeOf h := by
            have : 0 < sizeOf h + 1 := Nat.succ_pos _
            simpa [Nat.add_comm] using this
          have ht_lt : sizeOf t < sizeOf t + (1 + sizeOf h) :=
            Nat.lt_add_of_pos_right htpos
          have ht_lt' : sizeOf t < sizeOf (h :: t) := by
            simpa [List.cons.sizeOf_spec, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ht_lt
          exact Nat.lt_trans hlt ht_lt'

private theorem sizeOf_lt_sizeOf_pregame_mk_left
    (L R : List PreGame) (birth : Nat) {x : PreGame} (hx : x ∈ L) :
    sizeOf x < sizeOf ({ L := L, R := R, birth := birth } : PreGame) := by
  have hx' : sizeOf x < sizeOf L := sizeOf_lt_sizeOf_list_of_mem hx
  have hpos : 0 < (1 + sizeOf R + sizeOf birth) := by
    have : 0 < Nat.succ (sizeOf R + sizeOf birth) := Nat.succ_pos _
    simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
  have hlt : sizeOf L < sizeOf L + (1 + sizeOf R + sizeOf birth) :=
    Nat.lt_add_of_pos_right hpos
  have hL : sizeOf L < sizeOf ({ L := L, R := R, birth := birth } : PreGame) := by
    simpa [PreGame.mk.sizeOf_spec, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlt
  exact Nat.lt_trans hx' hL

private theorem sizeOf_lt_sizeOf_pregame_mk_right
    (L R : List PreGame) (birth : Nat) {x : PreGame} (hx : x ∈ R) :
    sizeOf x < sizeOf ({ L := L, R := R, birth := birth } : PreGame) := by
  have hx' : sizeOf x < sizeOf R := sizeOf_lt_sizeOf_list_of_mem hx
  have hpos : 0 < (1 + sizeOf L + sizeOf birth) := by
    have : 0 < Nat.succ (sizeOf L + sizeOf birth) := Nat.succ_pos _
    simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
  have hlt : sizeOf R < sizeOf R + (1 + sizeOf L + sizeOf birth) :=
    Nat.lt_add_of_pos_right hpos
  have hR : sizeOf R < sizeOf ({ L := L, R := R, birth := birth } : PreGame) := by
    -- reorder `sizeOf R + (...)` into `1 + sizeOf L + sizeOf R + sizeOf birth`
    simpa [PreGame.mk.sizeOf_spec, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlt
  exact Nat.lt_trans hx' hR

/-- Recompute birthdays and normalise leaves to `nullCut`. This makes
the evaluation/compilation story robust even if a user constructed an
inconsistent `PreGame` record manually. -/
def normalize : PreGame → PreGame
  | { L := [], R := [], .. } => nullCut
  | { L := L, R := R, .. } => PreGame.build (L.map normalize) (R.map normalize)
termination_by g => sizeOf g
decreasing_by
  all_goals
    first
    | exact sizeOf_lt_sizeOf_pregame_mk_left _ _ _ (by assumption)
    | exact sizeOf_lt_sizeOf_pregame_mk_right _ _ _ (by assumption)

/-! ## Canonical constructors (finite, dyadic-focused) -/

/-- Positive integers as pre-games: `0 := {∅|∅}`, `n+1 := {n|}`. -/
def natPreGame : Nat → PreGame
  | 0 => nullCut
  | Nat.succ n => PreGame.build [natPreGame n] []

/-- Negative integers as pre-games: `-1 := {|0}`, `-(n+2) := {|-(n+1)}`. -/
def negNatPreGame : Nat → PreGame
  | 0 => PreGame.build [] [nullCut]
  | Nat.succ n => PreGame.build [] [negNatPreGame n]

/-- Integers as pre-games. -/
def intPreGame : Int → PreGame
  | Int.ofNat n => natPreGame n
  | Int.negSucc n => negNatPreGame n

/-- Dyadic rationals `n / 2^k` as pre-games (finite approximation).

The recursion is on `k`; for odd numerators we use the canonical cut:
`n/2^(k+1) = { (n-1)/2^k  |  (n+1)/2^k }`.
-/
def dyadicPreGame (n : Int) : Nat → PreGame
  | 0 => intPreGame n
  | Nat.succ k =>
      if n % 2 = 0 then
        dyadicPreGame (n / 2) k
      else
        let nL := (n - 1) / 2
        let nR := (n + 1) / 2
        PreGame.build [dyadicPreGame nL k] [dyadicPreGame nR k]

namespace Compile

open Std

private def compileM : PreGame → StateM (Array Op) Nat
  | { L := [], R := [], .. } => do
      let i := (← get).size
      modify (·.push .unmark)
      return i
  | { L := L, R := R, .. } => do
      let lIdxs ← L.mapM compileM
      let rIdxs ← R.mapM compileM
      let i := (← get).size
      modify (·.push (.mark lIdxs rIdxs))
      return i
termination_by g => sizeOf g
decreasing_by
  all_goals
    first
    | exact sizeOf_lt_sizeOf_pregame_mk_left _ _ _ (by assumption)
    | exact sizeOf_lt_sizeOf_pregame_mk_right _ _ _ (by assumption)

/-- Compile a (normalised) `PreGame` into a well-formed flat program. -/
def compile (g : PreGame) : Program :=
  let gN := normalize g
  let (root, ops) := (compileM gN).run #[]
  { ops := ops, root := root }

/-- Compile and defensively re-check well-formedness. This should never
fail for programs emitted by `compile`, but keeps downstream executables
robust in the presence of future refactors. -/
def compileChecked (g : PreGame) : Except String Program :=
  let p := compile g
  if p.isWellFormed then
    .ok p
  else
    .error "internal error: compile produced an ill-formed program"

end Compile

end LoFProgram

end Surreal
end Numbers
end HeytingLean
