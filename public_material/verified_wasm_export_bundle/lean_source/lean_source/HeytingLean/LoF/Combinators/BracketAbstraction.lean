import HeytingLean.LoF.Combinators.SKY
import Std.Data.HashMap

/-!
# BracketAbstraction — λ → SKY compilation (Phase 2 scaffold)

This file provides a small *syntactic* bracket abstraction compiler:

* a combinator-expression syntax `CExp Var` that extends SKY with free variables,
* Turner's style abstraction elimination `[x]E`,
* a tiny untyped λ syntax `Lam Var`,
* and a compiler `Lam.compile` into `CExp Var`.

Correctness proofs (β/η simulation, optimization soundness) are planned follow-ups.
-/

namespace HeytingLean
namespace LoF
namespace Combinators

open HeytingLean.LoF

namespace Bracket

inductive BracketMode where
  | classic
  | bulk
  deriving Repr, DecidableEq

/-! ## Combinator expressions with variables -/

inductive CExp (Var : Type) where
  | var (v : Var)
  | K
  | S
  | Y
  | app (f a : CExp Var)
deriving Repr, DecidableEq

namespace CExp

variable {Var : Type}

def I : CExp Var :=
  .app (.app .S .K) .K

def occurs [DecidableEq Var] (x : Var) : CExp Var → Bool
  | .var v => decide (v = x)
  | .K => false
  | .S => false
  | .Y => false
  | .app f a => occurs x f || occurs x a

def opt [DecidableEq Var] : CExp Var → CExp Var
  | .app (.app .S (.app .K e)) (.app .K f) => .app .K (.app e f)
  | .app (.app .S (.app .K e)) a =>
      if a = I then e else .app (.app .S (.app .K e)) a
  | e => e

def bracket [DecidableEq Var] (x : Var) : CExp Var → CExp Var
  | .var v =>
      if v = x then I else .app .K (.var v)
  | .K => .app .K .K
  | .S => .app .K .S
  | .Y => .app .K .Y
  | .app f a =>
      if occurs x f || occurs x a then
        opt (.app (.app .S (bracket x f)) (bracket x a))
      else
        .app .K (.app f a)

def denote (ρ : Var → Comb) : CExp Var → Comb
  | .var v => ρ v
  | .K => .K
  | .S => .S
  | .Y => .Y
  | .app f a => .app (denote ρ f) (denote ρ a)

def erase : CExp PEmpty → Comb
  | .var v => nomatch v
  | .K => .K
  | .S => .S
  | .Y => .Y
  | .app f a => .app (erase f) (erase a)

def erase? : CExp Var → Option Comb
  | .var _ => none
  | .K => some .K
  | .S => some .S
  | .Y => some .Y
  | .app f a =>
      match erase? f, erase? a with
      | some f', some a' => some (.app f' a')
      | _, _ => none

end CExp

/-! ## Untyped lambda terms (named variables) -/

inductive Lam (Var : Type) where
  | var (v : Var)
  | app (f a : Lam Var)
  | lam (x : Var) (body : Lam Var)
  | K
  | S
  | Y
deriving Repr

namespace Lam

variable {Var : Type} [DecidableEq Var]

def compileClassic : Lam Var → CExp Var
  | .var v => .var v
  | .app f a => .app (compileClassic f) (compileClassic a)
  | .lam x body => CExp.bracket x (compileClassic body)
  | .K => .K
  | .S => .S
  | .Y => .Y

def compile : Lam Var → CExp Var :=
  compileClassic

def compileClosedClassic? (t : Lam Var) : Option Comb :=
  (compileClassic t).erase?

private def indexOfBinder? (x : Var) : List Var → Option Nat
  | [] => none
  | y :: ys =>
      if y = x then
        some 0
      else
        Nat.succ <$> indexOfBinder? x ys

private inductive DBLam where
  | var (idx : Nat)
  | app (f a : DBLam)
  | lam (body : DBLam)
  | K
  | S
  | Y
  deriving Repr, DecidableEq, Inhabited

private inductive BulkAtom where
  | K
  | S
  | Y
  | I
  | T
  | R
  | B (arity : Nat)
  | C (arity : Nat)
  | SFamily (arity : Nat)
  deriving Repr, DecidableEq, BEq, Hashable, Inhabited

private inductive OpenComb where
  | var (idx : Nat)
  | atom (a : BulkAtom)
  | app (f a : OpenComb)
  deriving Repr, DecidableEq, Inhabited

private abbrev Gamma := List Bool
private abbrev GammaComb := Gamma × OpenComb

private def openAppMany (f : OpenComb) (args : List OpenComb) : OpenComb :=
  args.foldl OpenComb.app f

private def lamAppMany (f : Lam Nat) (args : List (Lam Nat)) : Lam Nat :=
  args.foldl Lam.app f

private def lamBindMany (binders : List Nat) (body : Lam Nat) : Lam Nat :=
  binders.foldr Lam.lam body

private def mkBulkB (n : Nat) : BulkAtom :=
  .B (max 1 n)

private def mkBulkC (n : Nat) : BulkAtom :=
  .C (max 1 n)

private def mkBulkS (n : Nat) : BulkAtom :=
  .SFamily (max 1 n)

private def allTrue : Gamma → Bool
  | [] => true
  | true :: rest => allTrue rest
  | false :: _ => false

private def headRunLength [DecidableEq α] : List α → Nat
  | [] => 0
  | x :: xs =>
      let rec go : Nat → List α → Nat
        | n, [] => n
        | n, y :: ys =>
            if y = x then
              go (n + 1) ys
            else
              n
      go 1 xs

private def headPairRun : List (Bool × Bool) → Option ((Bool × Bool) × Nat)
  | [] => none
  | x :: xs => some (x, headRunLength (x :: xs))

private def splitHeadBoolRun : Gamma → Option (Bool × Nat × Gamma)
  | [] => none
  | g@(head :: _) =>
      let count := headRunLength g
      some (head, count, g.drop count)

private def namedToDB? : Lam Var → List Var → Option DBLam
  | .var v, env => DBLam.var <$> indexOfBinder? v env
  | .app f a, env => DBLam.app <$> namedToDB? f env <*> namedToDB? a env
  | .lam x body, env => DBLam.lam <$> namedToDB? body (x :: env)
  | .K, _ => some .K
  | .S, _ => some .S
  | .Y, _ => some .Y

partial def bulkPair : GammaComb → GammaComb → GammaComb
  | ([], d₁), ([], d₂) =>
      ([], .app d₁ d₂)
  | ([], d₁), ([true], .atom .I) =>
      ([true], d₁)
  | ([], d₁), (g₂, d₂) =>
      if d₂ = .atom .I && !g₂.isEmpty && allTrue g₂ then
        (g₂, .app (.atom (mkBulkB (g₂.length - 1))) d₁)
      else
        match splitHeadBoolRun g₂ with
        | some (head, count, post) =>
            let pre := List.replicate count head
            let d₁' := if head then .app (.atom (mkBulkB pre.length)) d₁ else d₁
            let (gOut, dOut) := bulkPair ([], d₁') (post, d₂)
            (pre ++ gOut, dOut)
        | none =>
            ([], .app d₁ d₂)
  | ([true], .atom .I), ([], d₂) =>
      ([true], .app (.atom .T) d₂)
  | (g₁, d₁), (g₂, .atom .I) =>
      match splitHeadBoolRun g₁ with
      | some (head, count, post) =>
          if g₂.isEmpty then
            if head then
              let lifted := openAppMany (.atom (mkBulkC 1)) [(.atom (mkBulkC count)), .atom .I]
              let (gOut, dOut) := bulkPair ([], lifted) (post, d₁)
              (List.replicate count true ++ gOut, dOut)
            else
              bulkPair (post, d₁) ([], .atom .I)
          else if g₁ = [true] && !g₂.headD true then
            let (gOut, dOut) := bulkPair ([], .atom .T) (g₂.tail, .atom .I)
            (true :: gOut, dOut)
          else if !g₁.headD true && g₂ = [true] then
            (true :: g₁.tail, d₁)
          else if allTrue g₂ && g₁.take g₂.length = List.replicate g₂.length false then
            let n := g₂.length
            let (gOut, dOut) := bulkPair ([], .atom (mkBulkB (n - 1))) (g₁.drop n, d₁)
            (g₂ ++ gOut, dOut)
          else
            match headPairRun (List.zip g₁ g₂) with
            | none => ([], d₁)
            | some ((b₁, b₂), pairCount) =>
                let leftRest : GammaComb := (g₁.drop pairCount, d₁)
                let rightRest : GammaComb := (g₂.drop pairCount, .atom .I)
                let (gOut, dOut) :=
                  match (b₁, b₂) with
                  | (false, false) => bulkPair leftRest rightRest
                  | (false, true) =>
                      let lifted := bulkPair ([], .atom (mkBulkB pairCount)) leftRest
                      bulkPair lifted rightRest
                  | (true, false) =>
                      let lifted := bulkPair ([], .atom (mkBulkC pairCount)) leftRest
                      bulkPair lifted rightRest
                  | (true, true) =>
                      let lifted := bulkPair ([], .atom (mkBulkS pairCount)) leftRest
                      bulkPair lifted rightRest
                (List.replicate pairCount (b₁ || b₂) ++ gOut, dOut)
      | none =>
          if !g₂.isEmpty && allTrue g₂ && g₁.take g₂.length = List.replicate g₂.length false then
            let n := g₂.length
            let (gOut, dOut) := bulkPair ([], .atom (mkBulkB (n - 1))) (g₁.drop n, d₁)
            (g₂ ++ gOut, dOut)
          else
            match headPairRun (List.zip g₁ g₂) with
            | none => ([], d₁)
            | some ((b₁, b₂), count) =>
                let leftRest : GammaComb := (g₁.drop count, d₁)
                let rightRest : GammaComb := (g₂.drop count, .atom .I)
                let (gOut, dOut) :=
                  match (b₁, b₂) with
                  | (false, false) => bulkPair leftRest rightRest
                  | (false, true) =>
                      let lifted := bulkPair ([], .atom (mkBulkB count)) leftRest
                      bulkPair lifted rightRest
                  | (true, false) =>
                      let lifted := bulkPair ([], .atom (mkBulkC count)) leftRest
                      bulkPair lifted rightRest
                  | (true, true) =>
                      let lifted := bulkPair ([], .atom (mkBulkS count)) leftRest
                      bulkPair lifted rightRest
                (List.replicate count (b₁ || b₂) ++ gOut, dOut)
  | (g₁, d₁), (g₂, d₂) =>
      match splitHeadBoolRun g₁ with
      | some (head, count, post) =>
          if g₂.isEmpty then
            if head then
              let lifted := openAppMany (.atom (mkBulkC 1)) [(.atom (mkBulkC count)), d₂]
              let (gOut, dOut) := bulkPair ([], lifted) (post, d₁)
              (List.replicate count true ++ gOut, dOut)
            else
              bulkPair (post, d₁) ([], d₂)
          else
            match headPairRun (List.zip g₁ g₂) with
            | none => ([], .app d₁ d₂)
            | some ((b₁, b₂), pairCount) =>
                let leftRest : GammaComb := (g₁.drop pairCount, d₁)
                let rightRest : GammaComb := (g₂.drop pairCount, d₂)
                let (gOut, dOut) :=
                  match (b₁, b₂) with
                  | (false, false) => bulkPair leftRest rightRest
                  | (false, true) =>
                      let lifted := bulkPair ([], .atom (mkBulkB pairCount)) leftRest
                      bulkPair lifted rightRest
                  | (true, false) =>
                      let lifted := bulkPair ([], .atom (mkBulkC pairCount)) leftRest
                      bulkPair lifted rightRest
                  | (true, true) =>
                      let lifted := bulkPair ([], .atom (mkBulkS pairCount)) leftRest
                      bulkPair lifted rightRest
                (List.replicate pairCount (b₁ || b₂) ++ gOut, dOut)
      | none =>
          match headPairRun (List.zip g₁ g₂) with
          | none => ([], .app d₁ d₂)
          | some ((b₁, b₂), count) =>
              let leftRest : GammaComb := (g₁.drop count, d₁)
              let rightRest : GammaComb := (g₂.drop count, d₂)
              let (gOut, dOut) :=
                match (b₁, b₂) with
                | (false, false) => bulkPair leftRest rightRest
                | (false, true) =>
                    let lifted := bulkPair ([], .atom (mkBulkB count)) leftRest
                    bulkPair lifted rightRest
                | (true, false) =>
                    let lifted := bulkPair ([], .atom (mkBulkC count)) leftRest
                    bulkPair lifted rightRest
                | (true, true) =>
                    let lifted := bulkPair ([], .atom (mkBulkS count)) leftRest
                    bulkPair lifted rightRest
              (List.replicate count (b₁ || b₂) ++ gOut, dOut)

partial def bulkOpt : DBLam → GammaComb
  | .var 0 => ([true], .atom .I)
  | .var (idx + 1) =>
      let (gamma, d) := bulkOpt (.var idx)
      (false :: gamma, d)
  | .app f a =>
      bulkPair (bulkOpt f) (bulkOpt a)
  | .lam body =>
      let (gamma, d) := bulkOpt body
      match gamma with
      | [] => ([], .app (.atom .K) d)
      | true :: tail => (tail, d)
      | false :: tail => bulkPair ([], .atom .K) (tail, d)
  | .K => ([], .atom .K)
  | .S => ([], .atom .S)
  | .Y => ([], .atom .Y)

private def bulkAtomLambda : BulkAtom → Lam Nat
  | .I =>
      lamBindMany [0] (.var 0)
  | .T =>
      lamBindMany [0, 1] (.app (.var 1) (.var 0))
  | .R =>
      lamBindMany [0, 1, 2] (lamAppMany (.var 1) [.var 2, .var 0])
  | .B arity =>
      let xs := (List.range arity).map (· + 2)
      lamBindMany ([0, 1] ++ xs) (.app (.var 0) (lamAppMany (.var 1) (xs.map Lam.var)))
  | .C arity =>
      let xs := (List.range arity).map (· + 2)
      lamBindMany ([0, 1] ++ xs) (lamAppMany (.var 0) ((xs.map Lam.var) ++ [.var 1]))
  | .SFamily arity =>
      let xs := (List.range arity).map (· + 2)
      lamBindMany ([0, 1] ++ xs)
        (lamAppMany (.var 0) ((xs.map Lam.var) ++ [lamAppMany (.var 1) (xs.map Lam.var)]))
  | .K => .K
  | .S => .S
  | .Y => .Y

private def lowerAtomCached (a : BulkAtom) : StateM (Std.HashMap BulkAtom Comb) (Option Comb) := do
  match a with
  | .K => pure (some .K)
  | .S => pure (some .S)
  | .Y => pure (some .Y)
  | .I => pure (some Comb.I)
  | other =>
      let cache ← get
      match cache.get? other with
      | some comb => pure (some comb)
      | none =>
          match compileClosedClassic? (Var := Nat) (bulkAtomLambda other) with
          | none => pure none
          | some comb =>
              modify fun st => st.insert other comb
              pure (some comb)

partial def lowerOpenCombM : OpenComb → StateM (Std.HashMap BulkAtom Comb) (Option Comb)
  | .var _ => pure none
  | .atom a => lowerAtomCached a
  | .app f a => do
      match (← lowerOpenCombM f), (← lowerOpenCombM a) with
      | some f', some a' => pure (some (.app f' a'))
      | _, _ => pure none

def compileClosedBulk? (t : Lam Var) : Option Comb := do
  let term ← namedToDB? t []
  let (gamma, raw) := bulkOpt term
  if !gamma.isEmpty then
    none
  else
    match lowerOpenCombM raw |>.run {} with
    | (some comb, _) => some comb
    | _ => none

@[noinline] def compileClosedWithMode? (mode : BracketMode) (t : Lam Var) : Option Comb :=
  match mode with
  | .classic => compileClosedClassic? t
  | .bulk => compileClosedBulk? t

def compileClosedBulkPublic? (t : Lam Var) : Option Comb :=
  compileClosedBulk? t

@[noinline] def compileClosed? (t : Lam Var) : Option Comb :=
  compileClosedWithMode? .classic t

end Lam

end Bracket
end Combinators
end LoF
end HeytingLean
