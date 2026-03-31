import Lean.Data.Json

/-!
# Surreal 3D lens lattice (structural)

This file provides a *structural* (non-semantic) lens lattice for
experiment bookkeeping. A "lens point" is a triple:

- a **semantic** lens (e.g. Dialectica, SheafOnℝ),
- a **computational** lens (e.g. Functional vs Method), and
- an **algebraic** lens (e.g. Tensor/Graph/Clifford bridges).

The main notion here is *composability* of a path through the lattice:
we allow steps that change **at most one axis at a time** (Hamming
distance ≤ 1). This matches the intuition of moving along edges of a
3D grid.

This is intentionally lightweight: the semantic meaning of each lens is
implemented elsewhere; here we only provide well-typed tags and a path
validator that can be exported in reports.
-/

namespace HeytingLean
namespace Numbers
namespace Surreal

open Lean

inductive SemanticLens where
  | eff
  | modified
  | lifschitz
  | relative
  | dialectica
  | sheafOnR
  deriving Repr, DecidableEq, Inhabited

def SemanticLens.toString : SemanticLens → String
  | .eff => "Eff"
  | .modified => "Modified"
  | .lifschitz => "Lifschitz"
  | .relative => "Relative"
  | .dialectica => "Dialectica"
  | .sheafOnR => "SheafOnR"

instance : ToString SemanticLens := ⟨SemanticLens.toString⟩

instance : ToJson SemanticLens := ⟨fun x => Json.str x.toString⟩

inductive ComputationalLens where
  | method
  | turing
  | functional
  deriving Repr, DecidableEq, Inhabited

def ComputationalLens.toString : ComputationalLens → String
  | .method => "Method"
  | .turing => "Turing"
  | .functional => "Functional"

instance : ToString ComputationalLens := ⟨ComputationalLens.toString⟩

instance : ToJson ComputationalLens := ⟨fun x => Json.str x.toString⟩

inductive AlgebraicLens where
  | core
  | tensor
  | graph
  | clifford
  deriving Repr, DecidableEq, Inhabited

def AlgebraicLens.toString : AlgebraicLens → String
  | .core => "Core"
  | .tensor => "Tensor"
  | .graph => "Graph"
  | .clifford => "Clifford"

instance : ToString AlgebraicLens := ⟨AlgebraicLens.toString⟩

instance : ToJson AlgebraicLens := ⟨fun x => Json.str x.toString⟩

/-- A point in the (semantic × computational × algebraic) lens lattice. -/
structure LensPoint where
  sem : SemanticLens
  comp : ComputationalLens
  alg : AlgebraicLens
  deriving Repr, DecidableEq

instance : ToJson LensPoint where
  toJson p :=
    Json.mkObj
      [ ("semantic", toJson p.sem)
      , ("computational", toJson p.comp)
      , ("algebraic", toJson p.alg)
      ]

def LensPoint.default : LensPoint :=
  { sem := .eff, comp := .functional, alg := .core }

/-- Number of coordinates that differ between two points. -/
def LensPoint.hamming (p q : LensPoint) : Nat :=
  (if p.sem = q.sem then 0 else 1)
  + (if p.comp = q.comp then 0 else 1)
  + (if p.alg = q.alg then 0 else 1)

/-- A step is compossible when it changes at most one axis. -/
def compossibleStep (p q : LensPoint) : Bool :=
  p.hamming q ≤ 1

/-- Validate a full path through the lattice. Empty and singleton paths are valid. -/
def compossiblePath : List LensPoint → Bool
  | [] => true
  | [_] => true
  | p :: q :: rest =>
      compossibleStep p q && compossiblePath (q :: rest)

end Surreal
end Numbers
end HeytingLean
