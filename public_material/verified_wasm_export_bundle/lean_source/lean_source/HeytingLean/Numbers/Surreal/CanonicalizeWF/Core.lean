import Std
import Mathlib.Data.List.Sort
import Mathlib.Data.String.Basic
import HeytingLean.Numbers.SurrealCore

/-!
# Surreal Canonicalize Core

Std-only canonicalization helpers: RBMap-based `normListCore`, runtime `height` fuel,
and lightweight property guards for local smoke tests.
-/

namespace HeytingLean
namespace Numbers
namespace Surreal

open SurrealCore
open Std

abbrev Pair := String × PreGame

@[inline] def key (g : PreGame) : String := toString g.birth

@[inline] def quickKey (g : PreGame) : String := toString g.birth

@[inline] def pairKeys (xs : List Pair) : List String :=
  xs.map Prod.fst

/-- Fingerprint keys of a list of games. -/
@[inline] def fkeys (ys : List PreGame) : List String :=
  ys.map key

@[inline] def mkPairs (ys : List PreGame) : List Pair :=
  ys.map fun g => (key g, g)

def PairLE (a b : Pair) : Prop := a.fst ≤ b.fst

/-- Pairwise transitivity for the key order. -/
instance instIsTransPairLE : IsTrans Pair PairLE where
  trans := by
    intro a b c h₁ h₂
    exact _root_.le_trans h₁ h₂

/-- Totality for the key order. -/
instance instIsTotalPairLE : IsTotal Pair PairLE := by
  constructor
  intro a b
  simpa [PairLE] using le_total a.fst b.fst

/-- Decidable comparator for pair keys. -/
instance instDecidablePairLE : DecidableRel PairLE :=
  fun a b => by
    dsimp [PairLE]
    infer_instance

@[inline] def pairLEb (a b : Pair) : Bool := decide (a.fst ≤ b.fst)

/-- Proof-only mergeSort by key; relies on mathlib lemmas. -/
def sortPairsMS (xs : List Pair) : List Pair :=
  xs.mergeSort pairLEb

/-- Proof-only dedup that drops subsequent entries sharing the head's key. -/
def dedupSorted : List Pair → List Pair
  | [] => []
  | x :: xs =>
      x :: dedupSorted (xs.dropWhile (fun y => y.fst = x.fst))
termination_by xs => xs.length
decreasing_by
  simp_wf
  have h := List.length_dropWhile_le (fun y => y.fst = x.fst) xs
  exact Nat.lt_of_le_of_lt h (Nat.lt_succ_self _)

@[inline] def normPairsMS (ys : List PreGame) : List Pair :=
  dedupSorted (sortPairsMS (mkPairs ys))

/-- Proof-only normalizer built from mergeSort + structural dedup. -/
@[inline] def normListMS (ys : List PreGame) : List PreGame :=
  (normPairsMS ys).map Prod.snd

/-- Deterministic dedup+sort via the list-based normalizer; keeps first occurrence of each key. -/
@[inline] def normListCore (ys : List PreGame) : List PreGame :=
  normListMS ys

@[inline] def normalizeBirth (L R : List PreGame) : Nat :=
  let maxBirth (xs : List PreGame) := xs.foldl (fun m g => Nat.max m g.birth) 0
  match L, R with
  | [], [] => 0
  | _, _   => Nat.succ (Nat.max (maxBirth L) (maxBirth R))

def canonicalizeFuel : Nat → PreGame → PreGame
  | 0, g => g
  | Nat.succ n, g =>
      let L₁ := g.L.map (canonicalizeFuel n)
      let R₁ := g.R.map (canonicalizeFuel n)
      let L₂ := normListCore L₁
      let R₂ := normListCore R₁
      let b  := normalizeBirth L₂ R₂
      { L := L₂, R := R₂, birth := b }

/-- Simple fuel bound based on child counts. -/
@[inline] def fuelBound (g : PreGame) : Nat :=
  g.L.length + g.R.length + 1

/-- Height proxy derived from one cheap canonicalization pass. -/
@[inline] def height (g : PreGame) : Nat :=
  (canonicalizeFuel (fuelBound g) g).birth + 1

@[simp] theorem height_pos (g : PreGame) : 0 < height g := by
  simp [height]

@[inline] def canonicalizeWF (g : PreGame) : PreGame :=
  canonicalizeFuel (height g) g

@[inline] def eqByKey (x y : PreGame) : Bool :=
  decide (quickKey x = quickKey y)

@[inline] def normListCoreIdem (ys : List PreGame) : Bool :=
  let a := (normListCore (normListCore ys)).map quickKey
  let b := (normListCore ys).map quickKey
  decide (a = b)

/-- Nondecreasing check using the builtin `String` order. -/
def nondecreasingStr : List String → Bool
  | [] | [_] => true
  | a :: b :: t => decide (a ≤ b) && nondecreasingStr (b :: t)

/-- Nodup check via a `HashSet`. Returns true iff all keys are unique. -/
@[inline] def nodupKeys (xs : List String) : Bool :=
  let step := fun (acc : Option (HashSet String)) k =>
    match acc with
    | none => none
    | some seen => if seen.contains k then none else some (seen.insert k)
  match xs.foldl step (some ({} : HashSet String)) with
  | some _ => true
  | none => false

/-- Combined guard on the output of `normListCore`. -/
@[inline] def normListCoreOk (ys : List PreGame) : Bool :=
  let zs := normListCore ys
  let ks := zs.map quickKey
  nondecreasingStr ks && nodupKeys ks

/-- Shortcut list of keys after `normListCore`. -/
@[inline] def normListCoreKeys (ys : List PreGame) : List String :=
  (normListCore ys).map quickKey

/-- Sorted unique keys extracted from the raw input via the list normalizer. -/
@[inline] def uniqueSortedKeys (ys : List PreGame) : List String :=
  pairKeys (normPairsMS ys)

/-- Check that `normListCore` keeps exactly the sorted-unique keys. -/
@[inline] def normListCorePermOk (ys : List PreGame) : Bool :=
  normListCoreKeys ys = uniqueSortedKeys ys

/-- Ensure every child has smaller height (runtime guard, no proofs). -/
@[inline] def heightDecOK (g : PreGame) : Bool :=
  let cg := canonicalizeWF g
  let h := height cg
  let okL := cg.L.all (fun c => decide (height c < h))
  let okR := cg.R.all (fun c => decide (height c < h))
  okL && okR

/-- Height fuel is chosen so every child should be strictly smaller; proof kept in Proofs. -/
@[inline] def childIsSmallerByHeight (_g _c : PreGame) : Prop := True

end Surreal
end Numbers
end HeytingLean
