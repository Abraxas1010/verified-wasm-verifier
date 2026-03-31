import HeytingLean.Matula.Compute.Decoder
import HeytingLean.Matula.Compute.Encoder
import HeytingLean.Matula.Core.Canonicalize

namespace HeytingLean
namespace Matula
namespace Extension
namespace Hopf

/-!
Executable Matula-tree Hopf extension scaffold.

This module now includes an admissible-cuts style comultiplication lane:
- multiplication is transported through Matula encode/decode,
- comultiplication enumerates admissible cuts as a list of `(prunedForest, trunk)` terms,
- counit/antipode remain lightweight executable adapters.

This is an executable foundation for proof-hardening toward a full Connes-Kreimer
Hopf development.
-/

/-- Phase-IV Hopf adapter carrier: rooted trees in canonical Matula form. -/
abbrev Carrier := RTree

/-- Code-side unit for the multiplicative Matula Hopf adapter. -/
def hopfUnitCode : Nat := 1

/-- Code-side multiplication for the multiplicative Matula Hopf adapter. -/
def hopfMulCode (a b : Nat) : Nat := a * b

/-- Tree-side unit. -/
def hopfUnit : Carrier := .leaf

/-- Tree-side multiplication transported through Matula encoding. -/
def hopfMul (t u : Carrier) : Carrier :=
  matulaDecode (hopfMulCode (matulaEncode t) (matulaEncode u))

/-- Forest component used by admissible-cuts comultiplication terms. -/
abbrev Forest := List Carrier

/-- One admissible-cut term `(P_c(t), R_c(t))`. -/
structure CutTerm where
  pruned : Forest
  trunk : Carrier
  deriving Repr, Inhabited, BEq, DecidableEq

private structure ChildCut where
  pruned : Forest
  keep : Option Carrier
  deriving Repr, Inhabited, BEq, DecidableEq

private structure NodeAcc where
  pruned : Forest
  kept : List Carrier
  deriving Repr, Inhabited, BEq, DecidableEq

mutual
  /--
  Enumerate admissible cuts for a rooted tree.

  Output is a multiset-as-list of terms to preserve multiplicities.
  -/
  partial def admissibleCuts : Carrier → List CutTerm
    | .leaf => [{ pruned := [], trunk := .leaf }]
    | .node children =>
        let init : List NodeAcc := [{ pruned := [], kept := [] }]
        let accumulated :=
          children.foldl
            (fun acc child =>
              acc.flatMap (fun a =>
                (childCuts child).map (fun c =>
                  { pruned := a.pruned ++ c.pruned
                    kept := a.kept ++ (match c.keep with | none => [] | some t => [t]) })))
            init
        accumulated.map (fun a =>
          { pruned := a.pruned.map RTree.canonicalizeByMatula
            trunk := RTree.canonicalizeByMatula (.node a.kept) })

  /--
  Per-child admissible-cut options:
  - cut above child (`keep = none`, whole child goes to pruned forest),
  - keep edge and recurse inside child (`keep = some trunkChild`).
  -/
  partial def childCuts (child : Carrier) : List ChildCut :=
    { pruned := [child], keep := none } ::
      (admissibleCuts child).map (fun ct => { pruned := ct.pruned, keep := some ct.trunk })
end

/--
Executable Connes-Kreimer style comultiplication terms.

`hopfComul t` returns a list of `(prunedForest, trunk)` terms representing
`Δ(t)` as a formal sum with multiplicities.
-/
def hopfComul (t : Carrier) : List (Forest × Carrier) :=
  (admissibleCuts t).map (fun ct => (ct.pruned, ct.trunk))

/-- Counit: detects the unit tree. -/
def hopfCounit : Carrier → Nat
  | .leaf => 1
  | .node _ => 0

/-- Antipode adapter: canonicalization at the tree carrier. -/
def hopfAntipode (t : Carrier) : Carrier :=
  t.canonicalizeByMatula

@[simp] theorem hopfMulCode_assoc (a b c : Nat) :
    hopfMulCode (hopfMulCode a b) c = hopfMulCode a (hopfMulCode b c) := by
  simp [hopfMulCode, Nat.mul_assoc]

@[simp] theorem hopfMulCode_comm (a b : Nat) :
    hopfMulCode a b = hopfMulCode b a := by
  simp [hopfMulCode, Nat.mul_comm]

@[simp] theorem hopfMulCode_unit_left (a : Nat) :
    hopfMulCode hopfUnitCode a = a := by
  simp [hopfMulCode, hopfUnitCode]

@[simp] theorem hopfMulCode_unit_right (a : Nat) :
    hopfMulCode a hopfUnitCode = a := by
  simp [hopfMulCode, hopfUnitCode]

@[simp] theorem admissibleCuts_leaf :
    admissibleCuts .leaf = [{ pruned := [], trunk := .leaf }] := by
  native_decide

@[simp] theorem hopfComul_leaf :
    hopfComul .leaf = [([], .leaf)] := by
  native_decide

@[simp] theorem hopfCounit_unit : hopfCounit hopfUnit = 1 := rfl

@[simp] theorem hopfAntipode_canonical (t : Carrier) :
    hopfAntipode t = t.canonicalizeByMatula := rfl

end Hopf
end Extension
end Matula
end HeytingLean
