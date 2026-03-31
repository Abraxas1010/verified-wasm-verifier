import Std
import HeytingLean.Topology.Knot.Braid
import HeytingLean.Topology.Knot.LaurentPoly

/-!
# Knot theory: Burau representation (executable, small)

Implements the reduced Burau representation over the executable Laurent polynomial carrier
`LaurentPoly` and uses the standard determinant formula to compute the single-variable Alexander
polynomial of a closed braid.

Scope:
- executable and small (intended for small strand counts used in fixtures/CLIs)
- determinant implemented for sizes up to 2 (i.e. up to 3 strands reduced Burau)

This is a computation-first integration point; proof-theoretic properties (e.g. Markov invariance)
are future work.
-/

namespace HeytingLean
namespace Topology
namespace Knot

open Std

namespace Burau

abbrev Poly := LaurentPoly

def t : Poly := LaurentPoly.mon 1 1
def tInv : Poly := LaurentPoly.mon (-1) 1

private def one : Poly := (1 : Poly)
private def zero : Poly := (0 : Poly)

abbrev Mat := Array (Array Poly)

instance : DecidableEq Mat := by
  unfold Mat
  infer_instance

instance : DecidableEq (Except String Mat) := by
  intro x y
  cases x <;> cases y
  · -- error / error
    simpa using (inferInstance : Decidable (_ = _))
  · -- error / ok
    exact isFalse (by intro h; cases h)
  · -- ok / error
    exact isFalse (by intro h; cases h)
  · -- ok / ok
    simpa using (inferInstance : Decidable (_ = _))

instance : DecidableEq (Except String Poly) := by
  intro x y
  cases x <;> cases y
  · simpa using (inferInstance : Decidable (_ = _))
  · exact isFalse (by intro h; cases h)
  · exact isFalse (by intro h; cases h)
  · simpa using (inferInstance : Decidable (_ = _))

private def matGet! (m : Mat) (i j : Nat) : Poly :=
  m[i]![j]!

private def matSet! (m : Mat) (i j : Nat) (v : Poly) : Mat :=
  m.set! i ((m[i]!).set! j v)

def matId (n : Nat) : Mat :=
  Array.ofFn (n := n) (fun (i : Fin n) =>
    Array.ofFn (n := n) (fun (j : Fin n) => if i = j then one else zero))

def matMul (a b : Mat) : Mat :=
  let n := a.size
  Array.ofFn (n := n) (fun (i : Fin n) =>
    Array.ofFn (n := n) (fun (j : Fin n) =>
      Id.run do
        let mut acc : Poly := 0
        for k in [0:n] do
          acc := acc + (matGet! a i.1 k) * (matGet! b k j.1)
        return acc))

def matSub (a b : Mat) : Mat :=
  let n := a.size
  Array.ofFn (n := n) (fun (i : Fin n) =>
    Array.ofFn (n := n) (fun (j : Fin n) => (matGet! a i.1 j.1) - (matGet! b i.1 j.1)))

private def det1 (m : Mat) : Poly :=
  matGet! m 0 0

private def det2 (m : Mat) : Poly :=
  let a := matGet! m 0 0
  let b := matGet! m 0 1
  let c := matGet! m 1 0
  let d := matGet! m 1 1
  a * d - b * c

def det (m : Mat) : Except String Poly := do
  match m.size with
  | 0 => pure 1
  | 1 => pure (det1 m)
  | 2 => pure (det2 m)
  | n => throw s!"Burau.det: unsupported size {n} (extend determinant implementation)"

def geomSeries (n : Nat) : Poly :=
  (List.range n).foldl (fun acc k => acc + LaurentPoly.mon (Int.ofNat k) 1) 0

def divByGeomSeries (n : Nat) (p : Poly) : Except String Poly := do
  if n = 0 then
    throw "divByGeomSeries: n=0"
  let d := geomSeries n
  if p = 0 then
    return 0
  let ts := p.toList
  let minP := (ts.head!).1
  let maxP := (ts.getLast!).1
  let maxQ := maxP - Int.ofNat (n - 1)
  if maxQ < minP then
    throw "divByGeomSeries: degree too small for quotient"
  let coeffAt (e : Int) : Int :=
    match ts.find? (fun (x, _) => x = e) with
    | some (_, c) => c
    | none => 0
  let lenQ : Nat := (maxQ - minP).toNat + 1
  let mut qArr : Array Int := Array.replicate lenQ 0
  for j in [0:lenQ] do
    let e := minP + Int.ofNat j
    let mut sumPrev : Int := 0
    for i in [1:n] do
      if i <= j then
        sumPrev := sumPrev + qArr[j - i]!
    qArr := qArr.set! j (coeffAt e - sumPrev)
  let mut qTerms : List (Int × Int) := []
  for j in [0:lenQ] do
    let c := qArr[j]!
    if c != 0 then
      qTerms := qTerms.concat (minP + Int.ofNat j, c)
  let q : Poly := { terms := qTerms }
  -- Verify exact division.
  if q * d = p then
    return q
  else
    throw "divByGeomSeries: not divisible"

private def burauBlockPos : Mat :=
  -- [[1 - t, t], [1, 0]] (unreduced 2x2 block, included for reference)
  #[
    #[one - t, t],
    #[one, zero]
  ]

private def burauBlockNeg : Mat :=
  -- inverse block: [[0, 1], [tInv, 1 - tInv]] (unreduced inverse block, included for reference)
  #[
    #[zero, one],
    #[tInv, one - tInv]
  ]

private def unitInv (p : Poly) : Except String Poly := do
  match p.toList with
  | [(e, c)] =>
      if c = 1 || c = -1 then
        pure (LaurentPoly.mon (-e) c)
      else
        throw "unitInv: coeff not a unit"
  | _ => throw "unitInv: not a monomial unit"

private def matInv (m : Mat) : Except String Mat := do
  match m.size with
  | 0 => pure #[]
  | 1 =>
      let a := matGet! m 0 0
      let aInv ← unitInv a
      pure #[#[aInv]]
  | 2 =>
      let a := matGet! m 0 0
      let b := matGet! m 0 1
      let c := matGet! m 1 0
      let d := matGet! m 1 1
      let detm := a * d - b * c
      let detInv ← unitInv detm
      pure #[
        #[detInv * d, detInv * (-b)],
        #[detInv * (-c), detInv * a]
      ]
  | n => throw s!"matInv: unsupported size {n}"

def genReducedPos (n : Nat) (i : Nat) : Except String Mat := do
  if n < 2 then
    throw "genReducedPos: n<2"
  if i + 1 >= n then
    throw s!"genReducedPos: index out of range i={i} (n={n})"
  if n = 2 then
    -- sigma_1 ↦ (-t)
    return #[#[-(t)]]
  -- n >= 3, size = n-1
  let mSize := n - 1
  let mut m := matId mSize
  if i = 0 then
    -- sigma_1 ↦ [[-t, 1], [0, 1]] ⊕ I
    m := matSet! m 0 0 (-(t))
    m := matSet! m 0 1 one
    m := matSet! m 1 0 zero
    m := matSet! m 1 1 one
    return m
  else if i = n - 2 then
    -- sigma_{n-1} ↦ I ⊕ [[1, 0], [t, -t]]
    let r := mSize - 2
    m := matSet! m r r one
    m := matSet! m r (r + 1) zero
    m := matSet! m (r + 1) r t
    m := matSet! m (r + 1) (r + 1) (-(t))
    return m
  else
    -- 2 <= i <= n-2 (1 <= i <= mSize-2 in 0-based)
    -- block rows/cols (i-1,i,i+1):
    -- [[1, 0, 0],
    --  [t, -t, 1],
    --  [0, 0, 1]]
    let r0 := i - 1
    let r1 := i
    let r2 := i + 1
    m := matSet! m r0 r0 one
    m := matSet! m r0 r1 zero
    m := matSet! m r0 r2 zero
    m := matSet! m r1 r0 t
    m := matSet! m r1 r1 (-(t))
    m := matSet! m r1 r2 one
    m := matSet! m r2 r0 zero
    m := matSet! m r2 r1 zero
    m := matSet! m r2 r2 one
    return m

def genReduced (n : Nat) (i : Nat) (sign : Reidemeister.CurlKind) : Except String Mat := do
  let mp ← genReducedPos n i
  match sign with
  | .pos => pure mp
  | .neg => matInv mp

def wordReduced (n : Nat) (gens : List Braid.Gen) : Except String Mat := do
  if n = 0 then
    throw "Burau.wordReduced: n=0"
  if n = 1 then
    return #[]
  let mut acc := matId (n - 1)
  for g in gens do
    let r ← genReduced n g.i g.sign
    acc := matMul acc r
  return acc

def alexanderOfClosedBraid (n : Nat) (gens : List Braid.Gen) : Except String Poly := do
  -- Alexander polynomial via reduced Burau: det(I - rho(beta)) / (1 + t + ... + t^(n-1)).
  let rho ← wordReduced n gens
  let detTerm ← det (matSub (matId rho.size) rho)
  divByGeomSeries n detTerm

end Burau

end Knot
end Topology
end HeytingLean
