import HeytingLean.Metrics.Magnitude.HomologyGroups

namespace HeytingLean
namespace Metrics
namespace Magnitude

universe u v

open Finset
open HeytingLean.Computational.Homology

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

/-- Product-chain generator in total degree `n`, split as `(p,q)` with `p+q=n`. -/
structure ProductChain (α : Type u) (β : Type v) [DecidableEq α] [DecidableEq β] (n : Nat) where
  p : Nat
  q : Nat
  hpq : p + q = n
  left : MagnitudeChain α p
  right : MagnitudeChain β q

/-- Family input for a Künneth-style map, indexed by bidegrees summing to `n`. -/
def KunnethInput (α : Type u) (β : Type v) [DecidableEq α] [DecidableEq β] (n : Nat) : Type (max u v) :=
  ∀ p q, p + q = n → (MagnitudeChain α p → ℤ) × (MagnitudeChain β q → ℤ)

/-- Chain-level Künneth map on separated inputs: evaluate both factors and multiply. -/
def kunnethMap (n : Nat) (F : KunnethInput α β n) :
    ProductChain α β n → ℤ
  | ⟨p, q, hpq, σ, τ⟩ =>
      let fg := F p q hpq
      fg.1 σ * fg.2 τ

theorem kunnethMap_eval (n : Nat) (F : KunnethInput α β n)
    (x : ProductChain α β n) :
    kunnethMap (α := α) (β := β) n F x =
      (F x.p x.q x.hpq).1 x.left * (F x.p x.q x.hpq).2 x.right := by
  cases x
  rfl

/-- Multiplicative separability of the chain-level Künneth map. -/
theorem kunnethMap_mul (n : Nat) (F : KunnethInput α β n)
    (x : ProductChain α β n) :
    ∃ f g : ℤ, kunnethMap (α := α) (β := β) n F x = f * g := by
  refine ⟨(F x.p x.q x.hpq).1 x.left, (F x.p x.q x.hpq).2 x.right, ?_⟩
  exact kunnethMap_eval (α := α) (β := β) n F x

/-- Betti convolution term for computational `F₂` complexes. -/
def bettiConvolution
    (C D : HeytingLean.Computational.Homology.ChainComplexF2) (n : Nat) : Nat :=
  Finset.sum (Finset.range (n + 1))
    (fun p => bettiFromComplex C p * bettiFromComplex D (n - p))

theorem bettiConvolution_zero
    (C D : HeytingLean.Computational.Homology.ChainComplexF2) :
    bettiConvolution C D 0 = bettiFromComplex C 0 * bettiFromComplex D 0 := by
  simp [bettiConvolution]

private def dimAt (C : ChainComplexF2) (k : Nat) : Nat :=
  match C.dims[k]? with
  | some d => d
  | none => 0

private def boundaryAt (C : ChainComplexF2) (k : Nat) : F2Matrix :=
  match C.boundaries[k]? with
  | some M => M
  | none => F2Matrix.zero (dimAt C k) (dimAt C (k + 1))

private def matrixGet (M : F2Matrix) (r c : Nat) : Bool :=
  match M.data[r]? with
  | some row =>
      match row[c]? with
      | some b => b
      | none => false
  | none => false

private def identityF2 (n : Nat) : F2Matrix :=
  { rows := n
    cols := n
    data := Array.ofFn (fun i : Fin n =>
      Array.ofFn (fun j : Fin n => decide (i = j))) }

private def kronF2 (A B : F2Matrix) : F2Matrix :=
  { rows := A.rows * B.rows
    cols := A.cols * B.cols
    data := Array.ofFn (fun r : Fin (A.rows * B.rows) =>
      let ra := if B.rows = 0 then 0 else r.1 / B.rows
      let rb := if B.rows = 0 then 0 else r.1 % B.rows
      Array.ofFn (fun c : Fin (A.cols * B.cols) =>
        let ca := if B.cols = 0 then 0 else c.1 / B.cols
        let cb := if B.cols = 0 then 0 else c.1 % B.cols
        matrixGet A ra ca && matrixGet B rb cb)) }

private def xorBlock (out : Array (Array Bool)) (rowOff colOff : Nat) (B : F2Matrix) :
    Array (Array Bool) := Id.run do
  let mut acc := out
  for r in [:B.rows] do
    let brow := B.data[r]!
    for c in [:B.cols] do
      if brow[c]! then
        let rr := rowOff + r
        let cc := colOff + c
        let row := acc[rr]!
        let old := row[cc]!
        acc := acc.set! rr (row.set! cc (Bool.xor old true))
  return acc

private def productDimAt (C D : ChainComplexF2) (n : Nat) : Nat :=
  Finset.sum (Finset.range (n + 1)) (fun p => dimAt C p * dimAt D (n - p))

private def productOffsets (C D : ChainComplexF2) (n : Nat) : Array Nat := Id.run do
  let mut offs : Array Nat := Array.mkEmpty (n + 1)
  let mut acc := 0
  for p in [:n + 1] do
    offs := offs.push acc
    acc := acc + (dimAt C p * dimAt D (n - p))
  return offs

/-- Degree-`n` boundary block matrix for the tensor-product chain complex over `F₂`.
Over `F₂`, the Leibniz sign is absorbed (`- = +`). -/
private def productBoundaryAt (C D : ChainComplexF2) (n : Nat) : F2Matrix := Id.run do
  let rows := productDimAt C D n
  let cols := productDimAt C D (n + 1)
  let tgtOff := productOffsets C D n
  let srcOff := productOffsets C D (n + 1)
  let mut out : Array (Array Bool) := Array.replicate rows (Array.replicate cols false)
  for p in [:n + 2] do
    let q := n + 1 - p
    let src := srcOff[p]!
    if p > 0 then
      let blkC := kronF2 (boundaryAt C (p - 1)) (identityF2 (dimAt D q))
      out := xorBlock out (tgtOff[p - 1]!) src blkC
    if q > 0 then
      let blkD := kronF2 (identityF2 (dimAt C p)) (boundaryAt D (q - 1))
      out := xorBlock out (tgtOff[p]!) src blkD
  return { rows := rows, cols := cols, data := out }

/-- Tensor-product chain complex up to degree `maxDeg` (inclusive). -/
def productComplexF2 (C D : ChainComplexF2) (maxDeg : Nat) : ChainComplexF2 :=
  { dims := Array.ofFn (fun i : Fin (maxDeg + 1) => productDimAt C D i.1)
    boundaries := Array.ofFn (fun i : Fin maxDeg => productBoundaryAt C D i.1) }

/-- Künneth verification predicate at finite cutoff `maxDeg`. -/
def KunnethHoldsUpTo (C D : ChainComplexF2) (maxDeg : Nat) : Prop :=
  ∀ n : Fin (maxDeg + 1),
    bettiFromComplex (productComplexF2 C D maxDeg) n.1 = bettiConvolution C D n.1

/-- Betti-level Künneth profile for complexes concentrated in degree `0`. -/
theorem kunneth_iso_profile
    (C D : HeytingLean.Computational.Homology.ChainComplexF2)
    (hC0 : bettiFromComplex C 0 = 1)
    (hD0 : bettiFromComplex D 0 = 1)
    (hCpos : ∀ k, 0 < k → bettiFromComplex C k = 0)
    (hDpos : ∀ k, 0 < k → bettiFromComplex D k = 0)
    (n : Nat) :
    bettiConvolution C D n = if n = 0 then 1 else 0 := by
  cases n with
  | zero =>
      simp [bettiConvolution_zero, hC0, hD0]
  | succ m =>
      have hsum : bettiConvolution C D (Nat.succ m) = 0 := by
        unfold bettiConvolution
        apply Finset.sum_eq_zero
        intro p hp
        by_cases hp0 : p = 0
        · subst hp0
          have hm : 0 < Nat.succ m := Nat.succ_pos m
          simp [hDpos _ hm]
        · have hpPos : 0 < p := Nat.pos_of_ne_zero hp0
          simp [hCpos _ hpPos]
      simp [hsum]

/-- Canonical projection from cycles to homology classes. -/
def cycleToHomologyClass {δ : Type u} [Fintype δ] [DecidableEq δ] (n : Nat) :
    magnitudeCyclesAddSubgroup (α := δ) n → magnitudeHomologyGroupAdd (α := δ) n :=
  QuotientAddGroup.mk

/-- Finite cover used for Mayer-Vietoris style gluing at chain degree `0`. -/
structure MagnitudeCover (α : Type u) [Fintype α] [DecidableEq α] where
  U : Finset α
  V : Finset α
  cover : U ∪ V = Finset.univ

variable {γ : Type u} [Fintype γ] [DecidableEq γ]

/-- Restriction of a global function to `U`. -/
def restrictU (C : MagnitudeCover γ) (f : γ → ℤ) : C.U → ℤ :=
  fun x => f x.1

/-- Restriction of a global function to `V`. -/
def restrictV (C : MagnitudeCover γ) (f : γ → ℤ) : C.V → ℤ :=
  fun x => f x.1

/-- Diagonal map `(global sections) → (sections on U) ⊕ (sections on V)`. -/
def diagonalPair (C : MagnitudeCover γ) (f : γ → ℤ) : (C.U → ℤ) × (C.V → ℤ) :=
  (restrictU C f, restrictV C f)

/-- Mayer-Vietoris difference map on overlaps. -/
def mvConnecting (C : MagnitudeCover γ) :
    (C.U → ℤ) × (C.V → ℤ) → (↑(C.U ∩ C.V) → ℤ)
  | (fU, fV) => fun x =>
      let hxU : x.1 ∈ C.U := (Finset.mem_inter.mp x.2).1
      let hxV : x.1 ∈ C.V := (Finset.mem_inter.mp x.2).2
      fU ⟨x.1, hxU⟩ - fV ⟨x.1, hxV⟩

/-- Compatibility condition on overlap sections. -/
def MVCompatible (C : MagnitudeCover γ) (fg : (C.U → ℤ) × (C.V → ℤ)) : Prop :=
  ∀ x : ↑(C.U ∩ C.V),
    let hxU : x.1 ∈ C.U := (Finset.mem_inter.mp x.2).1
    let hxV : x.1 ∈ C.V := (Finset.mem_inter.mp x.2).2
    fg.1 ⟨x.1, hxU⟩ = fg.2 ⟨x.1, hxV⟩

theorem mvConnecting_eq_zero_iff_compatible (C : MagnitudeCover γ)
    (fg : (C.U → ℤ) × (C.V → ℤ)) :
    mvConnecting C fg = 0 ↔ MVCompatible C fg := by
  constructor
  · intro h x
    have hx := congrArg (fun g => g x) h
    exact sub_eq_zero.mp (by simpa [mvConnecting] using hx)
  · intro h
    funext x
    exact sub_eq_zero.mpr (h x)

/-- Glue compatible local sections into a global section. -/
def glueFromCompatible (C : MagnitudeCover γ) (fg : (C.U → ℤ) × (C.V → ℤ))
    (_hcompat : MVCompatible C fg) : γ → ℤ :=
  fun a =>
    if haU : a ∈ C.U then
      fg.1 ⟨a, haU⟩
    else
      let haV : a ∈ C.V := by
        have haUnion : a ∈ C.U ∪ C.V := by simp [C.cover]
        exact (Finset.mem_union.mp haUnion).resolve_left haU
      fg.2 ⟨a, haV⟩

theorem glueFromCompatible_restrictU (C : MagnitudeCover γ)
    (fg : (C.U → ℤ) × (C.V → ℤ)) (hcompat : MVCompatible C fg) :
    restrictU C (glueFromCompatible C fg hcompat) = fg.1 := by
  funext x
  simp [restrictU, glueFromCompatible, x.2]

theorem glueFromCompatible_restrictV (C : MagnitudeCover γ)
    (fg : (C.U → ℤ) × (C.V → ℤ)) (hcompat : MVCompatible C fg) :
    restrictV C (glueFromCompatible C fg hcompat) = fg.2 := by
  funext x
  by_cases hxU : (x : γ) ∈ C.U
  · have hxUV : (x : γ) ∈ C.U ∩ C.V := Finset.mem_inter.mpr ⟨hxU, x.2⟩
    have hEq := hcompat ⟨(x : γ), hxUV⟩
    simp [restrictV, glueFromCompatible, hxU] at hEq ⊢
    exact hEq
  · simp [restrictV, glueFromCompatible, hxU]

/-- Mayer-Vietoris exactness witness at the direct-sum term:
kernel elements of `mvConnecting` glue to a global section. -/
theorem mv_exact_at_direct_sum (C : MagnitudeCover γ) (fg : (C.U → ℤ) × (C.V → ℤ))
    (hker : mvConnecting C fg = 0) :
    ∃ h : γ → ℤ, diagonalPair C h = fg := by
  have hcompat : MVCompatible C fg :=
    (mvConnecting_eq_zero_iff_compatible C fg).mp hker
  refine ⟨glueFromCompatible C fg hcompat, ?_⟩
  ext <;> simp [diagonalPair, glueFromCompatible_restrictU, glueFromCompatible_restrictV]

/-- Cardinality identity associated to a finite Mayer-Vietoris cover. -/
theorem mv_cover_cardinality (C : MagnitudeCover γ) :
    C.U.card + C.V.card = Fintype.card γ + (C.U ∩ C.V).card := by
  calc
    C.U.card + C.V.card = (C.U ∪ C.V).card + (C.U ∩ C.V).card := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Finset.card_union_add_card_inter C.U C.V).symm
    _ = Fintype.card γ + (C.U ∩ C.V).card := by
      simp [C.cover, Finset.card_univ]

/-- Chain-degree specialization of Mayer-Vietoris exactness:
instantiate the finite carrier with `MagnitudeChain α n`. -/
theorem mv_exact_at_chain_degree
    {δ : Type u} [Fintype δ] [DecidableEq δ] (n : Nat)
    (C : MagnitudeCover (MagnitudeChain δ n))
    (fg : (C.U → ℤ) × (C.V → ℤ))
    (hker : mvConnecting C fg = 0) :
    ∃ h : MagnitudeChain δ n → ℤ, diagonalPair C h = fg := by
  exact mv_exact_at_direct_sum C fg hker

end Magnitude
end Metrics
end HeytingLean
