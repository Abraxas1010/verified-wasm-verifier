import HeytingLean.Computational.Tensor.Core

/-
Tiny numeric utilities over `EmbVec` using `Array Float`.
- dot, add, scale
- EmbMat and matvec
This is intentionally lightweight and not optimized.
-/

namespace HeytingLean
namespace Computational
namespace Tensor

open EmbVec

@[simp] def zipMinF
    (f : Float → Float → Float)
    (xs : Array Float) (ys : Array Float) : Array Float :=
  let m := Nat.min xs.size ys.size
  Id.run do
    let mut out : Array Float := Array.mkEmpty m
    for i in [:m] do
      out := out.push (f xs[i]! ys[i]!)
    out

@[simp] def dot (x y : EmbVec) : Float :=
  let xs := x.data; let ys := y.data
  let prods := zipMinF (· * ·) xs ys
  prods.foldl (init := 0.0) (· + ·)

@[simp] def add (x y : EmbVec) : EmbVec :=
  let xs := x.data; let ys := y.data
  let zs := zipMinF (· + ·) xs ys
  { dim := zs.size, data := zs }

@[simp] def scale (a : Float) (x : EmbVec) : EmbVec :=
  { dim := x.dim, data := x.data.map (fun t => a * t) }

structure EmbMat where
  rows : Nat
  cols : Nat
  data : Array (Array Float)   -- row-major, each row length ≥ cols (extra ignored)

namespace EmbMat

@[simp] def fromRows (rs : List (List Float)) : EmbMat :=
  let rows := rs.length
  let cols := rs.foldl (init := 0) (fun acc r => Nat.max acc r.length)
  let arr  := Array.mk (rs.map fun r => Array.mk r)
  { rows := rows, cols := cols, data := arr }

@[simp] def eye (n : Nat) : EmbMat :=
  let rows := Id.run do
    let mut acc : Array (Array Float) := Array.mkEmpty n
    for i in [:n] do
      let mut row : Array Float := Array.replicate n 0.0
      row := row.set! i 1.0
      acc := acc.push row
    acc
  { rows := n, cols := n, data := rows }

  end EmbMat

@[simp] def matvec (M : EmbMat) (v : EmbVec) : EmbVec :=
  let n := M.rows
  let m := Nat.min M.cols v.dim
  let out := Id.run do
    let mut acc : Array Float := Array.mkEmpty n
    for i in [:n] do
      let row := M.data[i]!
      -- dot of row[0..m) with v[0..m)
      let tmp := Id.run do
        let mut s : Float := 0.0
        for j in [:m] do
          s := s + row[j]! * v.data[j]!
        s
      acc := acc.push tmp
    acc
  { dim := n, data := out }

@[simp] def matmul (A B : EmbMat) : EmbMat :=
  let n := A.rows
  let k := Nat.min A.cols B.rows
  let m := B.cols
  let rows := Id.run do
    let mut acc : Array (Array Float) := Array.mkEmpty n
    for i in [:n] do
      let rowA := A.data[i]!
      let mut rowC : Array Float := Array.mkEmpty m
      for j in [:m] do
        let s := Id.run do
          let mut t : Float := 0.0
          for p in [:k] do
            let bp := B.data[p]!
            t := t + rowA[p]! * bp[j]!
          t
        rowC := rowC.push s
      acc := acc.push rowC
    acc
  { rows := n, cols := m, data := rows }

end Tensor
end Computational
end HeytingLean
