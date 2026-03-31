import HeytingLean.Crypto.Lattice.NoiseMLWE

/-!
# Noise-correct homomorphic specification (MLWE-shaped)

This file provides a *spec-only* “homomorphic correctness” layer that connects the PQC lattice
bridge to an FHE-like interface.

Non-goals:
- no keygen/encryption algorithms;
- no multiplication/relinearization implementation;
- no security claims.

The one concrete, fully proved hook is **homomorphic addition** with explicit noise growth.
-/

namespace HeytingLean.Crypto.FHE

open HeytingLean.Crypto.Lattice

/-!
## Ciphertexts and semantic relation

We reuse `MLWEInstance` as the public ciphertext carrier (`⟨A,b⟩`).
The message is modeled as a shift term added to the MLWE RHS.
-/

/-- Semantic relation: `ct` “encrypts” `m` if `ct.b = ct.A*s + e + m` with bounded noise `e`. -/
def EncRel (P : MLWEParams) (β : Nat) (ct : MLWEInstance P) (m : ModVec P.k P.n P.q) : Prop :=
  ∃ s e, BoundedNatRep P β e ∧ ct.b = ct.A.mulVec s + e + m

/-!
## Homomorphic addition
-/

/-- Pointwise ciphertext addition (expects a shared `A`; the theorem below assumes that). -/
def addCt (P : MLWEParams) (ct1 ct2 : MLWEInstance P) : MLWEInstance P :=
  { A := ct1.A, b := ct1.b + ct2.b }

theorem coeffBound_add_le {q : Nat} (x y : Zq q) :
    coeffBound (x + y) ≤ coeffBound x + coeffBound y := by
  classical
  -- Compare `valMinAbs (x+y)` to the integer representative `valMinAbs x + valMinAbs y`.
  have hx : ((x.valMinAbs : ℤ) : ZMod q) = x := by
    simp
  have hy : ((y.valMinAbs : ℤ) : ZMod q) = y := by
    simp
  have hxy : (((x + y).valMinAbs : ℤ) : ZMod q) = (x.valMinAbs + y.valMinAbs : ℤ) := by
    -- Both sides cast to `x+y` in `ZMod q`.
    calc
      (((x + y).valMinAbs : ℤ) : ZMod q) = x + y := by
        simp
      _ = ((x.valMinAbs : ℤ) : ZMod q) + ((y.valMinAbs : ℤ) : ZMod q) := by
        simp [hx, hy]
      _ = (x.valMinAbs + y.valMinAbs : ℤ) := by
        simp [Int.cast_add]
  -- `valMinAbs` gives the minimum-absolute-value representative; use it to bound by the chosen rep.
  cases q with
  | zero =>
      -- `ZMod 0` is `ℤ` and `valMinAbs` is identity.
      simpa [coeffBound, ZMod.valMinAbs_def_zero] using (Int.natAbs_add_le x y)
  | succ q' =>
      haveI : NeZero (Nat.succ q') := ⟨Nat.succ_ne_zero q'⟩
      have hmin : (x + y).valMinAbs.natAbs ≤ (x.valMinAbs + y.valMinAbs).natAbs := by
        -- Apply the Mathlib lemma: if `x` is within `n/2`, it has minimal natAbs among reps.
        have hxle : (x + y).valMinAbs.natAbs ≤ (Nat.succ q') / 2 := by
          simpa using (ZMod.natAbs_valMinAbs_le (n := Nat.succ q') (x := x + y))
        -- `hxy` is the equality in `ZMod (succ q')` needed by `natAbs_min_of_le_div_two`.
        have hxy' : (((x + y).valMinAbs : ℤ) : ZMod (Nat.succ q')) =
            (x.valMinAbs + y.valMinAbs : ℤ) := by
          exact hxy
        exact ZMod.natAbs_min_of_le_div_two (n := Nat.succ q') _ _ hxy' hxle
      -- Finish with triangle inequality on `natAbs`.
      have htri : (x.valMinAbs + y.valMinAbs).natAbs ≤ x.valMinAbs.natAbs + y.valMinAbs.natAbs :=
        Int.natAbs_add_le _ _
      -- Unfold `coeffBound` and combine.
      have hmin' : coeffBound (x + y) ≤ (x.valMinAbs + y.valMinAbs).natAbs := by
        simpa [coeffBound] using hmin
      have htri' : (x.valMinAbs + y.valMinAbs).natAbs ≤ coeffBound x + coeffBound y := by
        simpa [coeffBound, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htri
      exact le_trans hmin' htri'

theorem boundedNatRep_add {P : MLWEParams} {β1 β2 : Nat}
    {e1 e2 : ModVec P.k P.n P.q} :
    BoundedNatRep P β1 e1 →
    BoundedNatRep P β2 e2 →
    BoundedNatRep P (β1 + β2) (e1 + e2) := by
  intro h1 h2 i j
  have hcoeff : coeffBound (e1 i j + e2 i j) ≤ coeffBound (e1 i j) + coeffBound (e2 i j) :=
    coeffBound_add_le (x := e1 i j) (y := e2 i j)
  exact le_trans hcoeff (Nat.add_le_add (h1 i j) (h2 i j))

theorem homAdd_correct {P : MLWEParams} {β1 β2 : Nat}
    {ct1 ct2 : MLWEInstance P} {m1 m2 : ModVec P.k P.n P.q}
    (hA : ct2.A = ct1.A)
    (h1 : EncRel P β1 ct1 m1)
    (h2 : EncRel P β2 ct2 m2) :
    EncRel P (β1 + β2) (addCt P ct1 ct2) (m1 + m2) := by
  rcases h1 with ⟨s1, e1, he1, hb1⟩
  rcases h2 with ⟨s2, e2, he2, hb2⟩
  have hb2' : ct2.b = ct1.A.mulVec s2 + e2 + m2 := by
    simpa [hA] using hb2
  refine ⟨s1 + s2, e1 + e2, boundedNatRep_add (P := P) he1 he2, ?_⟩
  ext i j
  simp [addCt, hb1, hb2', Matrix.mulVec_add, add_assoc, add_left_comm, add_comm]

/-!
## Homomorphic multiplication (interface only)
-/

structure HomomorphicMulSpec (P : MLWEParams) where
  mulCt : MLWEInstance P → MLWEInstance P → MLWEInstance P
  betaOut : Nat → Nat → Nat
  correct :
    ∀ {β1 β2 : Nat} {ct1 ct2 : MLWEInstance P} {m1 m2 : ModVec P.k P.n P.q},
      EncRel P β1 ct1 m1 →
      EncRel P β2 ct2 m2 →
      EncRel P (betaOut β1 β2) (mulCt ct1 ct2) (m1 * m2)

/-!
## Interface composition lemmas

These lemmas let downstream code “stage” correctness results without committing to a concrete
multiplication implementation.
-/

theorem homAddMul_left_correct {P : MLWEParams} (S : HomomorphicMulSpec P)
    {β1 β2 β3 : Nat}
    {ct1 ct2 ct3 : MLWEInstance P} {m1 m2 m3 : ModVec P.k P.n P.q}
    (hA : ct2.A = ct1.A)
    (h1 : EncRel P β1 ct1 m1)
    (h2 : EncRel P β2 ct2 m2)
    (h3 : EncRel P β3 ct3 m3) :
    EncRel P (S.betaOut (β1 + β2) β3) (S.mulCt (addCt P ct1 ct2) ct3) ((m1 + m2) * m3) := by
  exact S.correct (homAdd_correct (P := P) (hA := hA) h1 h2) h3

theorem homAddMul_right_correct {P : MLWEParams} (S : HomomorphicMulSpec P)
    {β1 β2 β3 : Nat}
    {ct1 ct2 ct3 : MLWEInstance P} {m1 m2 m3 : ModVec P.k P.n P.q}
    (hA : ct3.A = ct2.A)
    (h2 : EncRel P β2 ct2 m2)
    (h3 : EncRel P β3 ct3 m3)
    (h1 : EncRel P β1 ct1 m1) :
    EncRel P (S.betaOut β1 (β2 + β3)) (S.mulCt ct1 (addCt P ct2 ct3)) (m1 * (m2 + m3)) := by
  exact S.correct h1 (homAdd_correct (P := P) (hA := hA) h2 h3)

end HeytingLean.Crypto.FHE
