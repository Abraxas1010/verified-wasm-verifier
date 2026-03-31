import HeytingLean.PDE.Symbolic.Expr

namespace HeytingLean.PDE.Symbolic

/-! # Symbolic PDE Inspectors

This module currently provides structural inspection utilities for symbolic PDE
expressions. Algebraic simplification rules remain a future extension.
-/

mutual

/-- Depth of a scalar expression tree. -/
private def scalarDepth : ScalarExpr → Nat
  | .atom _ | .real _ => 0
  | .add l r | .mul l r | .div l r => 1 + max (scalarDepth l) (scalarDepth r)
  | .neg e | .sqrt e | .expI e | .dt e | .dtt e | .laplacian e | .biharmonic e =>
      1 + scalarDepth e
  | .divergence v => 1 + vectorDepth v
  | .inner l r => 1 + max (vectorDepth l) (vectorDepth r)

/-- Depth of a vector expression tree. -/
private def vectorDepth : VectorExpr → Nat
  | .atom _ | .zero => 0
  | .add l r | .convective l r => 1 + max (vectorDepth l) (vectorDepth r)
  | .scale c e => 1 + max (scalarDepth c) (vectorDepth e)
  | .grad s => 1 + scalarDepth s
  | .dt e | .neg e => 1 + vectorDepth e

end

mutual

/-- Collect atom names appearing in a scalar expression. -/
private def scalarAtoms : ScalarExpr → List String
  | .atom name => [name]
  | .real _ => []
  | .add l r | .mul l r | .div l r => scalarAtoms l ++ scalarAtoms r
  | .neg e | .sqrt e | .expI e | .dt e | .dtt e | .laplacian e | .biharmonic e =>
      scalarAtoms e
  | .divergence v => vectorAtoms v
  | .inner l r => vectorAtoms l ++ vectorAtoms r

/-- Collect atom names appearing in a vector expression. -/
private def vectorAtoms : VectorExpr → List String
  | .atom name => [name]
  | .zero => []
  | .add l r | .convective l r => vectorAtoms l ++ vectorAtoms r
  | .scale c e => scalarAtoms c ++ vectorAtoms e
  | .grad s => scalarAtoms s
  | .dt e | .neg e => vectorAtoms e

end

mutual

/-- Maximum differential order visible in the scalar expression. -/
private def scalarDiffOrder : ScalarExpr → Nat
  | .atom _ | .real _ => 0
  | .add l r | .mul l r | .div l r => max (scalarDiffOrder l) (scalarDiffOrder r)
  | .neg e | .sqrt e | .expI e => scalarDiffOrder e
  | .dt e => 1 + scalarDiffOrder e
  | .dtt e => max 2 (2 + scalarDiffOrder e)
  | .laplacian e => max 2 (scalarDiffOrder e)
  | .biharmonic e => max 4 (scalarDiffOrder e)
  | .divergence v => max 1 (vectorDiffOrder v)
  | .inner l r => max (vectorDiffOrder l) (vectorDiffOrder r)

/-- Maximum differential order visible in the vector expression. -/
private def vectorDiffOrder : VectorExpr → Nat
  | .atom _ | .zero => 0
  | .add l r | .convective l r => max (vectorDiffOrder l) (vectorDiffOrder r)
  | .scale c e => max (scalarDiffOrder c) (vectorDiffOrder e)
  | .grad s => max 1 (scalarDiffOrder s)
  | .dt e => 1 + vectorDiffOrder e
  | .neg e => vectorDiffOrder e

end

mutual

/-- Whether the scalar expression contains a time derivative. -/
private def scalarHasTimeDeriv : ScalarExpr → Bool
  | .atom _ | .real _ => false
  | .add l r | .mul l r | .div l r => scalarHasTimeDeriv l || scalarHasTimeDeriv r
  | .neg e | .sqrt e | .expI e | .laplacian e | .biharmonic e => scalarHasTimeDeriv e
  | .dt _ | .dtt _ => true
  | .divergence v => vectorHasTimeDeriv v
  | .inner l r => vectorHasTimeDeriv l || vectorHasTimeDeriv r

/-- Whether the vector expression contains a time derivative. -/
private def vectorHasTimeDeriv : VectorExpr → Bool
  | .atom _ | .zero => false
  | .add l r | .convective l r => vectorHasTimeDeriv l || vectorHasTimeDeriv r
  | .scale c e => scalarHasTimeDeriv c || vectorHasTimeDeriv e
  | .grad s => scalarHasTimeDeriv s
  | .dt _ => true
  | .neg e => vectorHasTimeDeriv e

end

mutual

/-- Maximum time-derivative order visible in the scalar expression. -/
private def scalarTimeOrder : ScalarExpr → Nat
  | .atom _ | .real _ => 0
  | .add l r | .mul l r | .div l r => max (scalarTimeOrder l) (scalarTimeOrder r)
  | .neg e | .sqrt e | .expI e | .laplacian e | .biharmonic e => scalarTimeOrder e
  | .dt e => 1 + scalarTimeOrder e
  | .dtt e => max 2 (2 + scalarTimeOrder e)
  | .divergence v => vectorTimeOrder v
  | .inner l r => max (vectorTimeOrder l) (vectorTimeOrder r)

/-- Maximum time-derivative order visible in the vector expression. -/
private def vectorTimeOrder : VectorExpr → Nat
  | .atom _ | .zero => 0
  | .add l r | .convective l r => max (vectorTimeOrder l) (vectorTimeOrder r)
  | .scale c e => max (scalarTimeOrder c) (vectorTimeOrder e)
  | .grad s => scalarTimeOrder s
  | .dt e => 1 + vectorTimeOrder e
  | .neg e => vectorTimeOrder e

end

mutual

/-- Maximum spatial-derivative order visible in the scalar expression. -/
private def scalarSpatialOrder : ScalarExpr → Nat
  | .atom _ | .real _ => 0
  | .add l r | .mul l r | .div l r => max (scalarSpatialOrder l) (scalarSpatialOrder r)
  | .neg e | .sqrt e | .expI e | .dt e | .dtt e => scalarSpatialOrder e
  | .laplacian e => max 2 (scalarSpatialOrder e)
  | .biharmonic e => max 4 (scalarSpatialOrder e)
  | .divergence v => max 1 (vectorSpatialOrder v)
  | .inner l r => max (vectorSpatialOrder l) (vectorSpatialOrder r)

/-- Maximum spatial-derivative order visible in the vector expression. -/
private def vectorSpatialOrder : VectorExpr → Nat
  | .atom _ | .zero => 0
  | .add l r | .convective l r => max (vectorSpatialOrder l) (vectorSpatialOrder r)
  | .scale c e => max (scalarSpatialOrder c) (vectorSpatialOrder e)
  | .grad s => max 1 (scalarSpatialOrder s)
  | .dt e => vectorSpatialOrder e
  | .neg e => vectorSpatialOrder e

end

namespace ScalarExpr

def depth (expr : ScalarExpr) : Nat :=
  scalarDepth expr

def atoms (expr : ScalarExpr) : List String :=
  scalarAtoms expr

def diffOrder (expr : ScalarExpr) : Nat :=
  scalarDiffOrder expr

def hasTimeDeriv (expr : ScalarExpr) : Bool :=
  scalarHasTimeDeriv expr

def timeOrder (expr : ScalarExpr) : Nat :=
  scalarTimeOrder expr

def spatialOrder (expr : ScalarExpr) : Nat :=
  scalarSpatialOrder expr

end ScalarExpr

namespace VectorExpr

def depth (expr : VectorExpr) : Nat :=
  vectorDepth expr

def atoms (expr : VectorExpr) : List String :=
  vectorAtoms expr

def diffOrder (expr : VectorExpr) : Nat :=
  vectorDiffOrder expr

def hasTimeDeriv (expr : VectorExpr) : Bool :=
  vectorHasTimeDeriv expr

def timeOrder (expr : VectorExpr) : Nat :=
  vectorTimeOrder expr

def spatialOrder (expr : VectorExpr) : Nat :=
  vectorSpatialOrder expr

end VectorExpr

end HeytingLean.PDE.Symbolic
