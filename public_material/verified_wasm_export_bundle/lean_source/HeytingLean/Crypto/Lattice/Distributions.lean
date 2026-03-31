import HeytingLean.Crypto.RNG.Seeded
import Mathlib.Data.Int.Lemmas

namespace HeytingLean
namespace Crypto
namespace Lattice
namespace Dist

open HeytingLean.Crypto.RNG

/-!
# Deterministic sampling façades (toy/executable)

This file provides simple **deterministic** samplers used by toy models and tests.

Notes:
- These are *not* cryptographically faithful to Kyber/Dilithium sampling.
- The goal is to replace the “all zeros” placeholders with total, stable APIs that can be used
  to build executable models and deterministic tests.
- For KAT parity, the C reference harnesses under `WIP/pqc_lattice/` remain authoritative.
-/

/-- Seed wrapper for deterministic sampling. -/
structure Seed where
  bytes : ByteArray
  deriving DecidableEq

abbrev Sample := Int

private def natOfBytesLE (bs : ByteArray) : Nat := Id.run do
  let mut acc : Nat := 0
  let mut pow : Nat := 1
  for b in bs.data do
    acc := acc + pow * b.toNat
    pow := pow * 256
  return acc

/-!
## Bit-counting helper

This is used by the deterministic CBD sampler. We implement it recursively (rather than via a
mutable loop) so we can prove basic bounds about it.
-/

def popcountLow (x : Nat) : Nat → Nat
  | 0 => 0
  | bits + 1 => popcountLow x bits + (if x.testBit bits then 1 else 0)

theorem popcountLow_le (x bits : Nat) : popcountLow x bits ≤ bits := by
  induction bits with
  | zero => simp [popcountLow]
  | succ bits ih =>
      have hbit : (if x.testBit bits then 1 else 0) ≤ 1 := by
        split <;> omega
      -- `popcountLow x (bits+1) = popcountLow x bits + (if ...)`.
      -- Apply the induction hypothesis and add the last bit.
      have : popcountLow x bits + (if x.testBit bits then 1 else 0) ≤ bits + 1 :=
        Nat.add_le_add ih hbit
      simpa [popcountLow, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this

/-!
## Byte/bit stream helpers

To align more closely with FIPS-style samplers, we treat the seeded RNG as a little-endian
bitstream so we can:
- consume exactly `2*eta` bits per CBD sample (no wasted padding bits), and
- implement unbiased `uniformMod` via rejection sampling on `k = ⌈log₂ q⌉` bits.
-/

private structure BitStream where
  rng : SeededRNG
  buf : Nat
  bits : Nat

private def bitstreamInit (s : Seed) : BitStream :=
  { rng := SeededRNG.init s.bytes, buf := 0, bits := 0 }

private def bitstreamTake (k : Nat) (st : BitStream) : Nat × BitStream := Id.run do
  let mut rng := st.rng
  let mut buf := st.buf
  let mut bits := st.bits
  while bits < k do
    let (bs, rng') := SeededRNG.nextBytes rng 1
    rng := rng'
    let b : Nat := (bs.get! 0).toNat
    buf := buf + b * (2 ^ bits)
    bits := bits + 8
  let mask : Nat := 2 ^ k
  let out := buf % mask
  buf := buf / mask
  bits := bits - k
  return (out, { rng := rng, buf := buf, bits := bits })

private def bitsNeeded (q : Nat) : Nat := Id.run do
  let mut bits : Nat := 0
  let mut pow : Nat := 1
  while pow < q do
    pow := pow * 2
    bits := bits + 1
  return bits

/-- Centered binomial sampler using `2*eta` bits per output.

Implementation: consume exactly `2*eta` bits from a little-endian bitstream and compute
`popcount(low eta bits) - popcount(next eta bits)`.
-/
private def centeredBinomialSample (eta x : Nat) : Sample :=
  let a := popcountLow x eta
  let b := popcountLow (x / (2 ^ eta)) eta
  (a : ℤ) - (b : ℤ)

private theorem centeredBinomialSample_natAbs_le (eta x : Nat) :
    Int.natAbs (centeredBinomialSample eta x) ≤ eta := by
  -- `a,b ≤ eta` since `popcountLow` counts at most `eta` bits.
  have ha : popcountLow x eta ≤ eta := popcountLow_le x eta
  have hb : popcountLow (x / (2 ^ eta)) eta ≤ eta := popcountLow_le (x / (2 ^ eta)) eta
  simpa [centeredBinomialSample] using Int.natAbs_coe_sub_coe_le_of_le ha hb

private def centeredBinomialAux (eta : Nat) : Nat → BitStream → Array Sample → Array Sample
  | 0, _st, out => out
  | n + 1, st, out =>
      let (x, st') := bitstreamTake (2 * eta) st
      centeredBinomialAux eta n st' (out.push (centeredBinomialSample eta x))

/-- Centered binomial sampler using `2*eta` bits per output. -/
def centeredBinomial (eta : Nat) (s : Seed) (n : Nat) : Array Sample :=
  centeredBinomialAux eta n (bitstreamInit s) (Array.mkEmpty n)

theorem centeredBinomial_size (eta : Nat) (s : Seed) (n : Nat) :
    (centeredBinomial eta s n).size = n := by
  -- Helper: `centeredBinomialAux` increases size by `m`.
  have haux :
      ∀ m st out,
        (centeredBinomialAux eta m st out).size = out.size + m := by
    intro m
    induction m with
    | zero =>
        intro st out
        simp [centeredBinomialAux]
    | succ m ih =>
        intro st out
        simp [centeredBinomialAux, ih, Nat.add_left_comm, Nat.add_comm]
  -- Apply helper with empty output.
  simpa [centeredBinomial, bitstreamInit] using (haux n (bitstreamInit s) (Array.mkEmpty n))

theorem centeredBinomial_get_natAbs_le (eta : Nat) (s : Seed) (n : Nat) (i : Fin n) :
    Int.natAbs ((centeredBinomial eta s n)[i.1]'(by
      have hsize : (centeredBinomial eta s n).size = n := centeredBinomial_size (eta := eta) (s := s) (n := n)
      -- `i.2 : i.1 < n`; transport across `size = n`.
      exact Nat.lt_of_lt_of_eq i.2 hsize.symm)) ≤ eta := by
  -- Prove a stronger list-level invariant by induction on the auxiliary.
  have haux :
      ∀ m st out,
        (∀ x ∈ out.toList, Int.natAbs x ≤ eta) →
        (∀ x ∈ (centeredBinomialAux eta m st out).toList, Int.natAbs x ≤ eta) := by
    intro m
    induction m with
    | zero =>
        intro st out hout
        simpa [centeredBinomialAux] using hout
    | succ m ih =>
        intro st out hout
        cases h : bitstreamTake (2 * eta) st with
        | mk x0 st' =>
        -- Extend the invariant to `out.push (sample ...)`.
        have hout' : ∀ x ∈ (out.push (centeredBinomialSample eta x0)).toList, Int.natAbs x ≤ eta := by
          intro x hx
          have hx' : x ∈ out.toList ++ [centeredBinomialSample eta x0] := by
            simpa [Array.toList_push] using hx
          have : x ∈ out.toList ∨ x = centeredBinomialSample eta x0 := by
            simpa [List.mem_append, List.mem_singleton] using hx'
          cases this with
          | inl hxIn => exact hout x hxIn
          | inr hxEq =>
              rcases hxEq with rfl
              exact centeredBinomialSample_natAbs_le eta x0
        -- Now apply the induction hypothesis to the rest of the recursion.
        simpa [centeredBinomialAux, h] using ih st' (out.push (centeredBinomialSample eta x0)) hout'
  -- Apply the invariant starting from the empty output array.
  have hlist :
      ∀ x ∈ (centeredBinomial eta s n).toList, Int.natAbs x ≤ eta := by
    have hempty : ∀ x ∈ (Array.mkEmpty n : Array Sample).toList, Int.natAbs x ≤ eta := by
      intro _x hx
      cases hx
    simpa [centeredBinomial, centeredBinomialAux, bitstreamInit] using haux n (bitstreamInit s) (Array.mkEmpty n) hempty
  -- Turn the list property into the desired pointwise bound.
  have hmem : (centeredBinomial eta s n)[i.1]'(by
      have hsize : (centeredBinomial eta s n).size = n := centeredBinomial_size (eta := eta) (s := s) (n := n)
      exact Nat.lt_of_lt_of_eq i.2 hsize.symm) ∈ (centeredBinomial eta s n).toList := by
    -- Membership via `xs[i] ∈ xs` and `mem_toList_iff`.
    have : (centeredBinomial eta s n)[i.1]'(by
      have hsize : (centeredBinomial eta s n).size = n := centeredBinomial_size (eta := eta) (s := s) (n := n)
      exact Nat.lt_of_lt_of_eq i.2 hsize.symm) ∈ (centeredBinomial eta s n) := by
      exact Array.getElem_mem (xs := centeredBinomial eta s n) (i := i.1)
        (by
          have hsize : (centeredBinomial eta s n).size = n := centeredBinomial_size (eta := eta) (s := s) (n := n)
          exact Nat.lt_of_lt_of_eq i.2 hsize.symm)
    exact (Array.mem_toList_iff).2 this
  exact hlist _ hmem

/-- Uniform sampler `0..q-1` using 32-bit little-endian blocks.

This uses rejection sampling on `k = ⌈log₂ q⌉` bits to avoid modulo bias.
-/
def uniformMod (q : Nat) (s : Seed) (n : Nat) : Array Sample := Id.run do
  if q ≤ 1 then
    return Array.replicate n 0
  let k := bitsNeeded q
  let mut st := bitstreamInit s
  let mut out : Array Sample := Array.mkEmpty n
  for _i in [0:n] do
    let mut y : Nat := q
    while y ≥ q do
      let (cand, st') := bitstreamTake k st
      st := st'
      y := cand
    out := out.push (Int.ofNat y)
  return out

end Dist
end Lattice
end Crypto
end HeytingLean
