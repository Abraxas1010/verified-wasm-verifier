import Mathlib.Data.List.Basic

import HeytingLean.Layouts.Nested.NestCategory
import HeytingLean.Layouts.Nested.Refinement

/-!
# Pullback / pushforward along refinements (nested tuples)

Executable versions of `Nest_morphism.pullback_along` / `pushforward_along` from the companion
implementation (`ColfaxResearch/layout-categories`).

All operations return `Option` instead of throwing.
-/

namespace HeytingLean
namespace Layouts
namespace Nested

open NestedTuple

namespace NestMorphism

private def indexOf1? (x : ℕ) : List ℕ → Option ℕ
  | [] => none
  | y :: ys =>
      if x = y then
        some 1
      else
        (indexOf1? x ys).map Nat.succ

/-- Pull back a morphism along a refinement of its codomain. -/
def pullbackAlong? (f : NestMorphism) (refinement : NestedTuple) : Option NestMorphism := do
  let S := f.domain
  let T := f.codomain
  let Tprime := refinement
  if NestedTuple.refinesB Tprime T = false then
    none
  else
    let idxs : List ℕ := (List.range S.length).map Nat.succ
    let rec go (idxs : List ℕ) (replsRev : List NestedTuple) (mapRev : List ℕ) :
        Option (List NestedTuple × List ℕ) := do
      match idxs with
      | [] => pure (replsRev.reverse, mapRev.reverse)
      | i :: is =>
          let mapVal ← f.map[i.pred]?
          match mapVal with
          | 0 =>
              let leafVal ← S.entry? i
              let repl := NestedTuple.leaf leafVal
              go is (repl :: replsRev) (0 :: mapRev)
          | j =>
              let rel ← NestedTuple.relativeMode? Tprime j T
              let off ← NestedTuple.sublength? Tprime j T
              let newIdxs := (List.range rel.length).map (fun k => off + k + 1)
              go is (rel :: replsRev) (newIdxs.reverse ++ mapRev)

    let (repls, mapOut) ← go idxs [] []
    let Sprime ← S.sub repls
    NestMorphism.mk? Sprime Tprime mapOut

/-- Push forward a morphism along a refinement of its domain. -/
def pushforwardAlong? (f : NestMorphism) (refinement : NestedTuple) : Option NestMorphism := do
  let U := f.domain
  let V := f.codomain
  let Uprime := refinement
  if NestedTuple.refinesB Uprime U = false then
    none
  else
    -- Build the refined codomain `Vprime`.
    let idxsV : List ℕ := (List.range V.length).map Nat.succ
    let rec goV (idxs : List ℕ) (replsRev : List NestedTuple) : Option (List NestedTuple) := do
      match idxs with
      | [] => pure replsRev.reverse
      | j :: js =>
          if decide (j ∈ f.map) then
            let i ← indexOf1? j f.map
            let rel ← NestedTuple.relativeMode? Uprime i U
            goV js (rel :: replsRev)
          else
            let leafVal ← V.entry? j
            goV js (NestedTuple.leaf leafVal :: replsRev)

    let replsV ← goV idxsV []
    let Vprime ← V.sub replsV

    -- Build the pushed-forward map `Uprime ⟶ Vprime`.
    let idxsU : List ℕ := (List.range U.length).map Nat.succ
    let rec goMap (idxs : List ℕ) (accRev : List ℕ) : Option (List ℕ) := do
      match idxs with
      | [] => pure accRev.reverse
      | i :: is =>
          let mapVal ← f.map[i.pred]?
          match mapVal with
          | 0 =>
              let rel ← NestedTuple.relativeMode? Uprime i U
              let zeros := List.replicate rel.length 0
              goMap is (zeros.reverse ++ accRev)
          | j =>
              let rel ← NestedTuple.relativeMode? Vprime j V
              let off ← NestedTuple.sublength? Vprime j V
              let newIdxs := (List.range rel.length).map (fun k => off + k + 1)
              goMap is (newIdxs.reverse ++ accRev)

    let mapOut ← goMap idxsU []
    NestMorphism.mk? Uprime Vprime mapOut

/-- Weak composite via mutual refinement + pullback/pushforward (Python `weak_composite`). -/
def weakComposite? (f g : NestMorphism) : Option NestMorphism := do
  let T := f.codomain
  let U := g.domain
  let (Tprime, Uprime) ← NestedTuple.mutualRefinement? T U

  let inclMap : List ℕ := (List.range Tprime.length).map Nat.succ
  let inclusion ← NestMorphism.mk? Tprime Uprime inclMap

  let fprime ← pullbackAlong? f Tprime
  let gprime ← pushforwardAlong? g Uprime
  let fg ← fprime.compose? inclusion
  fg.compose? gprime

end NestMorphism

end Nested
end Layouts
end HeytingLean

