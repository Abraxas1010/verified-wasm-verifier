import HeytingLean.CCI.Core
import HeytingLean.CCI.RewriteTable
import HeytingLean.CCI.Cert

/-!
# CCI Checker (v1)

Deterministic replay of rewrites (identity in v1), simple canonicalization,
and digest verification. No JSON decoding here; tests construct `Certificate`
values directly.
-/

namespace HeytingLean
namespace CCI

/-- Apply rewrites by ID in order. v1 table is identity. -/
def applyRewrites (e : Expr) (rws : List RuleId) : Expr :=
  rws.foldl (fun acc rid => (applyById rid acc).getD acc) e

private def ord (a b : Expr) : Bool := a.structuralKey ≤ b.structuralKey

private def insertSorted (x : Expr) (xs : List Expr) : List Expr :=
  match xs with
  | [] => [x]
  | y :: ys => if ord x y then x :: xs else y :: insertSorted x ys

private def sortByKey (xs : List Expr) : List Expr :=
  xs.foldl (fun acc x => insertSorted x acc) []

private def dedupSorted (xs : List Expr) : List Expr :=
  match xs with
  | [] => []
  | x :: rest =>
      let rec go (prevKey : String) (ys : List Expr) : List Expr :=
        match ys with
        | [] => []
        | z :: zs =>
            let kz := z.structuralKey
            if kz = prevKey then go prevKey zs else z :: go kz zs
      x :: go x.structuralKey rest

private def decomposeAnd : Expr → List Expr
  | .andR a b => decomposeAnd a ++ decomposeAnd b
  | e => [e]

private def decomposeOr : Expr → List Expr
  | .orR a b => decomposeOr a ++ decomposeOr b
  | e => [e]

private def foldAnd (xs : List Expr) : Expr :=
  match xs with
  | [] => CCI.top
  | [x] => x
  | x :: ys => ys.foldl (fun acc y => .andR acc y) x

private def foldOr (xs : List Expr) : Expr :=
  match xs with
  | [] => CCI.bot
  | [x] => x
  | x :: ys => ys.foldl (fun acc y => .orR acc y) x

/-- Simple canonicalization: push implication to `¬a ∨ b`, drop double negation,
    and sort the children of commutative nodes (`andR`/`orR`). -/
def canon : Expr → Expr
  | .atom id    => .atom id
  | .notR a      =>
      match canon a with
      | .notR a' => a'
      | a' => .notR a'
  | .impR a b    =>
      -- canon (a ⇒ b) = canon (¬a ∨ b), but avoid a recursive call on a constructed term.
      let a' := canon a
      let b' := canon b
      let notA :=
        match a' with
        | .notR x => x
        | x => .notR x
      let lst := sortByKey (dedupSorted (decomposeOr (.orR notA b')))
      foldOr lst
  | .andR a b   =>
      let a' := canon a
      let b' := canon b
      let lst := sortByKey (dedupSorted (decomposeAnd (.andR a' b')))
      foldAnd lst
  | .orR a b    =>
      let a' := canon a
      let b' := canon b
      let lst := sortByKey (dedupSorted (decomposeOr (.orR a' b')))
      foldOr lst
  | .bvar idx => .bvar idx
  | .sort u => .sort u
  | .const n us => .const n us
  | .app f a => .app (canon f) (canon a)
  | .lam n bi ty body => .lam n bi (canon ty) (canon body)
  | .forallE n bi ty body => .forallE n bi (canon ty) (canon body)
  | .letE n ty val body => .letE n (canon ty) (canon val) (canon body)
  | .lit v => .lit v
  | .proj s idx body => .proj s idx (canon body)
  | .fvar n => .fvar n
  | .mvar n => .mvar n

/-- Verify digests contain the omega digest matching `hashExpr (canon (applyRewrites ...))`. -/
def check (cert : Certificate) : Bool :=
  let e' := applyRewrites cert.omega cert.rewrites
  let ec := canon e'
  let dh := hashExpr ec
  match cert.digests.find? (fun (p, _) => p = "omega") with
  | some (_, d) => d = dh
  | none        => false

end CCI
end HeytingLean
