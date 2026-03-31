import Mathlib.Data.List.Basic

import HeytingLean.Layouts.Nested.Profile

/-!
# Nested tuple morphisms (`Nest_morphism`-style, executable)

This is an algorithmic port of the companion implementation in
`ColfaxResearch/layout-categories` (`Nest_morphism` in `categories.py`).

We model a morphism `S ⟶ T` by:
- a domain `S : NestedTuple`,
- a codomain `T : NestedTuple`,
- a list `map : List ℕ` of length `S.length`, where `0` is the basepoint and `j+1` denotes the
  `j`-th leaf in `T.flatten`.

The primary focus is on *computability* (operations return `Option` instead of throwing).
-/

namespace HeytingLean
namespace Layouts
namespace Nested

open NestedTuple

/-- Morphisms between nested tuples (lying over a pointed injection on flattened leaves). -/
structure NestMorphism where
  domain : NestedTuple
  codomain : NestedTuple
  /-- Map on flattened leaf indices: length = `domain.length`, values in `[0, codomain.length]`. -/
  map : List ℕ
  deriving Repr, DecidableEq

namespace NestMorphism

private def labelsOk (domFlat codFlat : List ℕ+) (map : List ℕ) : Bool :=
  let rec go (idx : ℕ) (map : List ℕ) : Bool :=
    match map with
    | [] => true
    | v :: vs =>
        match v with
        | 0 => go (idx + 1) vs
        | Nat.succ k =>
            match domFlat[idx]?, codFlat[k]? with
            | some d, some c => decide (d = c) && go (idx + 1) vs
            | _, _ => false
  go 0 map

/-- Validity check (total, boolean).

Matches `_validate_inputs` for `Nest_morphism` in the Python reference:
- correct map length,
- values in range,
- no duplicate nonzero values,
- dimension label preservation on flattened leaves.
-/
def isValid (f : NestMorphism) : Bool :=
  let m := f.domain.length
  let n := f.codomain.length
  if f.map.length != m then
    false
  else if f.map.any (fun v => n < v) then
    false
  else
    let nonzero := f.map.filter (fun v => decide (v ≠ 0))
    if nonzero.eraseDups.length != nonzero.length then
      false
    else
      labelsOk f.domain.flatten f.codomain.flatten f.map

/-- Smart constructor returning `none` for invalid morphisms. -/
def mk? (domain codomain : NestedTuple) (map : List ℕ) : Option NestMorphism :=
  let f : NestMorphism := ⟨domain, codomain, map⟩
  if f.isValid then some f else none

/-- Composition `g ∘ f` (returns `none` if non-composable or invalid). -/
def compose? (f g : NestMorphism) : Option NestMorphism := do
  if f.codomain ≠ g.domain then
    none
  else
    let newMap ← f.map.mapM (fun v =>
      match v with
      | 0 => some 0
      | Nat.succ k => g.map[k]?)
    mk? f.domain g.codomain newMap

private def disjointImages (map1 map2 : List ℕ) : Bool :=
  let img1 := map1.filter (fun v => decide (v ≠ 0))
  let img2 := map2.filter (fun v => decide (v ≠ 0))
  !(img1.any (fun v => decide (v ∈ img2)))

/-- Concatenation `(f,g)` (wedge) when codomains agree and images are disjoint. -/
def concat? (f g : NestMorphism) : Option NestMorphism := do
  if f.codomain ≠ g.codomain then
    none
  else if disjointImages f.map g.map = false then
    none
  else
    let domain := NestedTuple.node [f.domain, g.domain]
    mk? domain f.codomain (f.map ++ g.map)

/-- `true` iff `0` is not in the image list (so a complement exists). -/
def isComplementable (f : NestMorphism) : Bool :=
  !(decide (0 ∈ f.map))

/-- Complement morphism `fᶜ` (returns `none` if not complementable). -/
def complement? (f : NestMorphism) : Option NestMorphism := do
  if f.isComplementable = false then
    none
  else
    let image : List ℕ := f.map
    let codFlat := f.codomain.flatten
    let idxs : List ℕ := (List.range codFlat.length).map Nat.succ
    let keepIdxs := idxs.filter (fun j => decide (j ∉ image))
    let domLeaves ← keepIdxs.mapM (fun j => do
      let leafVal ← codFlat[j.pred]?
      pure (NestedTuple.leaf leafVal))
    let domain := NestedTuple.node domLeaves
    mk? domain f.codomain keepIdxs

/-- Logical division: `f ⊘ g = f ∘ (g, gᶜ)` (returns `none` if preconditions fail). -/
def logicalDivide? (f g : NestMorphism) : Option NestMorphism := do
  let gc ← g.complement?
  let pair ← g.concat? gc
  pair.compose? f

/-- Logical product: `f ⊗ g = (f, g ∘ fᶜ)` (returns `none` if preconditions fail). -/
def logicalProduct? (f g : NestMorphism) : Option NestMorphism := do
  let fc ← f.complement?
  let right ← g.compose? fc
  f.concat? right

end NestMorphism

end Nested
end Layouts
end HeytingLean
