import HeytingLean.Physics.String.QSeries

/-
Modular action on truncated q-series via small NxN matrices.

This module implements a finite-dimensional stand-in for modular S/T
actions on q-series coefficients and a simple canonicalization nucleus
selecting a lexicographically minimal representative in a bounded
{S,T}-orbit. It is designed for demos and tests, not as a full arithmetic
theory, but the semantics are precise and fully specified.
-/

namespace HeytingLean
namespace Physics
namespace String

open HeytingLean.Physics.String

structure ModMatrices where
  S : Array (Array Float)
  T : Array (Array Float)

namespace ModMatrices

@[simp] def dim (M : ModMatrices) : Nat :=
  if M.S.size = 0 then 0 else M.S[0]!.size

end ModMatrices

@[simp] def applyMat (M : Array (Array Float)) (v : Array Float) : Array Float := Id.run do
  let n := v.size
  let mut out : Array Float := Array.replicate n 0.0
  for i in [:n] do
    let row := M[i]!
    let mut s : Float := 0.0
    for j in [:n] do
      s := s + row[j]! * v[j]!
    out := out.set! i s
  out

@[simp] def stepOrbit (M : ModMatrices) (v : Array Float) : Array (Array Float) :=
  #[(applyMat M.S v), (applyMat M.T v)]

@[simp] def lexico (a b : Array Float) : Bool := Id.run do
  let n := min a.size b.size
  for i in [:n] do
    if a[i]! < b[i]! then return true
    if a[i]! > b[i]! then return false
  return a.size ≤ b.size

@[simp] def canonical (M : ModMatrices) (v0 : Array Float) (steps : Nat) : Array Float := Id.run do
  let mut best := v0
  let mut frontier : Array (Array Float) := #[v0]
  let mut seen : Array (Array Float) := #[]
  for _k in [:steps] do
    let mut next : Array (Array Float) := #[]
    for v in frontier do
      let ns := stepOrbit M v
      for u in ns do
        next := next.push u
        -- update best by lexicographic order
        if lexico u best then best := u
    -- crude dedup by stringification
    let mut tmp : Array String := #[]
    let mut frontier' : Array (Array Float) := #[]
    for u in next do
      let key := toString u
      if !(tmp.contains key) then
        tmp := tmp.push key
        frontier' := frontier'.push u
    frontier := frontier'
    seen := seen ++ frontier
  return best

structure QNucleus where
  mats  : ModMatrices
  steps : Nat := 8

namespace QNucleus

@[simp] def project (N : QNucleus) (q : QSeries) : QSeries :=
  { coeffs := canonical N.mats q.coeffs N.steps }

end QNucleus

end String
end Physics
end HeytingLean
