import HeytingLean.Crypto.Lattice.NTTIterative
import HeytingLean.Crypto.Lattice.NTTCorrectness
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Basic

/-!
# NTT algorithm ↔ algebraic bridge (scaffolding)

This module is the *landing zone* for the remaining ML-KEM NTT verification gap:
connecting the executable Cooley–Tukey routine (`NTTIterative.nttIterative`) to an algebraic
specification.

What exists today:
- `HeytingLean.Crypto.Lattice.NTTCorrectness` proves **spec-level** invertibility and
  multiplication correctness using a CRT ring isomorphism for `Rq = (ZMod 3329)[X]/(X^256+1)`.
- `HeytingLean.Crypto.Lattice.NTTIterative` provides an **executable** iterative NTT/INTT
  skeleton over `Array (ZMod 3329)` (bit-reversal + twiddle table).

What is still open:
- a refinement theorem that the iterative algorithm computes the same transform as the algebraic
  NTT (up to the expected output ordering conventions).

External proof structure reference:
- Isabelle AFP: "Number_Theoretic_Transform" (Ammer & Kreuzer, 2022),
  key theorem `FNTT_correct` (fast NTT equals algebraic NTT).

Repo policy note:
This file intentionally contains **no** placeholder proofs. The main bridge theorem is tracked as
a conjecture (see `conjectures/mlkem_ntt_correctness.json`).
-/

namespace HeytingLean
namespace Crypto
namespace Lattice
namespace NTTBridge

open scoped BigOperators

abbrev q : Nat := NTT.q
abbrev F : Type := ZMod q

open NTTIterative

/-!
## A small, proved lemma we can rely on immediately
-/

theorem butterfly_algebraic (a b zk : F) :
    let (u, v) := butterfly a b zk
    u = a + zk * b ∧ v = a - zk * b := by
  simp [butterfly]

/-!
## Algebraic DFT-like specification (length 256)

For `q = 3329`, there is **no** element of order `512` in `ZMod q` because `q-1 = 256*13`. As a
result, ML-KEM’s NTT for the negacyclic ring `(ZMod q)[X]/(X^256+1)` cannot be specified as a plain
length-256 DFT into base-field values.

Instead, the algebraic CRT proof in `NTTCorrectness` decomposes `X^256+1` into **quadratic** factors
`X^2 - μ` indexed by primitive 256th roots `μ`. Each factor ring `K[X]/(X^2-μ)` has the basis
`{1, X}`, so a value in the factor can be represented as a pair `(a0, a1)` corresponding to
`a0 + a1*X`.

The executable `NTTIterative.nttIterative` produces an `Array` of length 256 which is naturally
interpreted as 128 such pairs; `NTTIterative.basemul` is precisely multiplication in these quadratic
factors.
-/

def arrayToFn (a : Array F) : Fin 256 → F :=
  fun i => a.getD i.1 0

def fnToArray (f : Fin 256 → F) : Array F :=
  Array.ofFn f

/-!
## Bridge conjecture (statement-only)

The intended final statement is that `nttIterative` computes the same map as the CRT-based
decomposition in `NTTCorrectness`, expressed at the **pair** level:

Given coefficients `a₀,…,a₂₅₅`, define polynomials in `Y`:
- `f0(Y) = ∑ₖ a₂ₖ Y^k` (even coefficients)
- `f1(Y) = ∑ₖ a₂ₖ₊₁ Y^k` (odd coefficients)

For each primitive 256th root `μ`, the remainder of `f(X)` modulo `X^2-μ` is:
`f0(μ) + X * f1(μ)`.

We record this as a `Prop` so downstream code can reference the exact goal without introducing
placeholder proofs.
-/

/-- The (computable) quadratic-factor specification of ML-KEM’s NTT output ordering. -/
def quadSpecMatrix : Matrix (Fin 256) (Fin 256) F :=
  fun j i =>
    let r : Nat := j.val / 2
    let pos : Nat := j.val % 2
    let rev : Nat := bitRevNat 7 r % 128
    let μ : F := (NTT.zeta : F) ^ (2 * rev + 1)
    if i.val % 2 = pos then
      μ ^ (i.val / 2)
    else
      0

def quadraticSpec (a : Array F) : Array F :=
  Array.ofFn (fun j : Fin 256 =>
    (quadSpecMatrix.mulVec (fun i : Fin 256 => a.getD i.val 0)) j)

noncomputable def nttIterative_matches_quadraticSpec : Prop :=
  ∀ (a : Array F) (h : a.size = 256),
    nttIterative a h = quadraticSpec a

end NTTBridge
end Lattice
end Crypto
end HeytingLean
