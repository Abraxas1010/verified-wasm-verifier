import HeytingLean.Chem.Materials.SLICES.Syntax
import Mathlib.Data.List.Sort
import Mathlib.Data.String.Basic

/-!
# SLICES: computable codec + canonicalization (benchmark/runtime support)

The Phase 1-3 "spec" modules in this repo prioritize mathematical structure and proofs. Some of the
spec-layer definitions (`encode`, `canonEncode`) are `noncomputable` because they traverse `Finset`s
using `toList`.

This file provides a **computable** companion implementation intended for:
- executable benchmarks (`slices_bench`)
- cross-runtime exports (Lean -> C/WASM) in later phases

It uses an explicit list/array representation (rather than `Finset`) so that sorting and
canonicalization produce executable code.
-/

namespace HeytingLean.Chem.Materials.SLICES

open HeytingLean.Chem.PeriodicTable

structure CEdge where
  u : Nat
  v : Nat
  t : TranslationVec
  deriving Repr, DecidableEq

structure CGraph where
  labels : Array Element
  edges : Array CEdge
  deriving Repr

def CGraph.n (g : CGraph) : Nat := g.labels.size

private def cmpNat (a b : Nat) : Ordering :=
  compare a b

private def cmpInt (a b : Int) : Ordering :=
  compare a b

private def cmpTranslation (a b : TranslationVec) : Ordering :=
  match cmpInt a.x b.x with
  | .eq =>
      match cmpInt a.y b.y with
      | .eq => cmpInt a.z b.z
      | o => o
  | o => o

def CEdge.cmp (a b : CEdge) : Ordering :=
  match cmpNat a.u b.u with
  | .eq =>
      match cmpNat a.v b.v with
      | .eq => cmpTranslation a.t b.t
      | o => o
  | o => o

def CEdge.leBool (a b : CEdge) : Bool :=
  match CEdge.cmp a b with
  | .gt => false
  | _ => true

def encodeC (g : CGraph) : String :=
  let atoms : List String := g.labels.toList.map symbol
  let edges : List CEdge := (g.edges.toList).mergeSort (fun a b => CEdge.leBool a b)
  let edgeTokens : List String :=
    edges.flatMap (fun e =>
      [toString e.u, toString e.v, toString e.t.x, toString e.t.y, toString e.t.z])
  String.intercalate " " (atoms ++ edgeTokens)

private def invertPerm (p : Array Nat) : Array Nat :=
  let n := p.size
  let rec go (i : Nat) (inv : Array Nat) : Array Nat :=
    if h : i < n then
      let j := p[i]!
      go (i + 1) (inv.set! j i)
    else
      inv
  go 0 (Array.replicate n 0)

private def permuteC (g : CGraph) (p : Array Nat) : CGraph :=
  let n := g.n
  let inv := invertPerm p
  let labels' : Array Element :=
    (Array.range n).map (fun i => g.labels[inv[i]!]!)
  let edges' : Array CEdge :=
    g.edges.map (fun e =>
      { u := p[e.u]!, v := p[e.v]!, t := e.t })
  { labels := labels', edges := edges' }

private def leString (a b : String) : Bool :=
  match compare a b with
  | .gt => false
  | _ => true

private def insertAssoc (k : String) (i : Nat) : List (String × List Nat) → List (String × List Nat)
  | [] => [(k, [i])]
  | (k', is) :: rest =>
      if k = k' then
        (k', i :: is) :: rest
      else
        (k', is) :: insertAssoc k i rest

private def labelGroups (g : CGraph) : List (List Nat) :=
  let n := g.n
  let idxs : List Nat := List.range n
  let pairs : List (String × List Nat) :=
    idxs.foldl
      (fun acc i =>
        let k := symbol (g.labels[i]!)
        insertAssoc k i acc)
      []
  let pairs := pairs.map (fun (k, is) => (k, is.reverse))
  let pairs := pairs.mergeSort (fun a b => leString a.1 b.1)
  pairs.map (fun kv => kv.2)

private def ordersFromGroups : List (List Nat) → List (List Nat)
  | [] => [[]]
  | grp :: rest =>
      let tails := ordersFromGroups rest
      (grp.permutations).foldl
        (fun acc p => acc ++ (tails.map (fun t => p ++ t)))
        []

private def invFromOrd (ord : Array Nat) : Array Nat :=
  let n := ord.size
  let rec go (i : Nat) (inv : Array Nat) : Array Nat :=
    if h : i < n then
      let old := ord[i]!
      go (i + 1) (inv.set! old i)
    else
      inv
  go 0 (Array.replicate n 0)

private def permuteCByOrd (g : CGraph) (ord : Array Nat) : CGraph :=
  let n := g.n
  if ord.size != n then
    g
  else
    let inv := invFromOrd ord
    let labels' : Array Element :=
      (Array.range n).map (fun i => g.labels[ord[i]!]!)
    let edges' : Array CEdge :=
      g.edges.map (fun e =>
        { u := inv[e.u]!, v := inv[e.v]!, t := e.t })
    { labels := labels', edges := edges' }

def canonEncodeC (g : CGraph) : Except String String := do
  let n := g.n
  if n = 0 then
    throw "canonEncodeC: empty label array"
  let base : List Nat := List.range n
  let perms : List (List Nat) := base.permutations
  match perms with
  | [] => throw "canonEncodeC: no permutations (unexpected)"
  | p0 :: ps =>
      let best0 := encodeC (permuteC g (p0.toArray))
      let best :=
        ps.foldl
          (fun best p =>
            let s := encodeC (permuteC g (p.toArray))
            if s < best then s else best)
          best0
      return best

def canonEncodeCLabelSorted (g : CGraph) : Except String String := do
  let n := g.n
  if n = 0 then
    throw "canonEncodeCLabelSorted: empty label array"
  let groups := labelGroups g
  let ords : List (List Nat) := ordersFromGroups groups
  match ords with
  | [] => throw "canonEncodeCLabelSorted: no orders (unexpected)"
  | o0 :: os =>
      let best0 := encodeC (permuteCByOrd g (o0.toArray))
      let best :=
        os.foldl
          (fun best o =>
            let s := encodeC (permuteCByOrd g (o.toArray))
            if s < best then s else best)
          best0
      return best

def decodeC? (s : String) : Except String CGraph := do
  let p ← parse s
  let n := p.atoms.length
  if n = 0 then
    throw "SLICES decode: empty atom list."
  let labels : Array Element := p.atoms.toArray
  let edges : Array CEdge :=
    (p.edges.map (fun e =>
      { u := e.u, v := e.v, t := e.t })).toArray
  return { labels := labels, edges := edges }

end HeytingLean.Chem.Materials.SLICES
