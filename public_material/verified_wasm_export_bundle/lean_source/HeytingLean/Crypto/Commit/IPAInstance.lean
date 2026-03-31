import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fin.Basic
import HeytingLean.Crypto.Commit.PedersenAssumptions
import HeytingLean.Crypto.Commit.Spec

/-!
# Crypto.Commit.IPAInstance

IPA-style vector-commitment instance for the current `Vec.Scheme` interface with
explicit randomness and a single-group Pedersen-style commitment map.

This module upgrades the earlier transparent-tag midpoint to a real single-group
commitment shape:

* `commit v r = r • H + Σ_i v_i • G_i`;
* openings reveal the full vector together with the blinding scalar; and
* the proved results are still the algebraic binding/opening theorems that the
  existing `Vec.Scheme` consumers need.

That is an honest midpoint:

* `OpenCorrect` and `OpenSound` are genuinely proved;
* the demo path uses no axioms;
* `verificationConsistencyAt` is wired to the current spec-level canonical
  opening invariant from `Vec.Scheme`; and
* the remaining computational-hiding content is exposed through the named
  assumption surface in `Crypto.Commit.PedersenAssumptions`.

In particular, the current `Vec.Scheme` interface has no adversary / oracle
language, so this module exposes only the weak interface-level
`VerificationConsistencyAt` property. Real hiding statements must be supplied
through `SecurityProps.computationalHidingAt`, not inferred from correctness.
-/

namespace HeytingLean
namespace Crypto
namespace Commit
namespace IPAInstance

open scoped BigOperators
open HeytingLean.Crypto.Commit.Spec

/-- Parameters for an IPA-style vector commitment over an additive group. -/
structure Params (n : Nat) (G : Type) [AddCommGroup G] where
  generators : Fin n → G
  blindingGenerator : G

/-- Linear binding component induced by the generator family. -/
def commitVector {n : Nat} {G : Type} [AddCommGroup G]
    (P : Params n G) (v : Fin n → Int) : G :=
  ∑ i, v i • P.generators i

/-- Pedersen-style commitment map with explicit blinding scalar. -/
def pedersenCommit {n : Nat} {G : Type} [AddCommGroup G]
    (P : Params n G) (v : Fin n → Int) (r : Int) : G :=
  r • P.blindingGenerator + commitVector P v

/-- Binding-level injectivity for the Pedersen commitment map. -/
def Binding {n : Nat} {G : Type} [AddCommGroup G] (P : Params n G) : Prop :=
  Function.Injective (fun vr : (Fin n → Int) × Int => pedersenCommit P vr.1 vr.2)

/-- Named discrete-log hardness surface attached to a concrete Pedersen
parameter instance. -/
abbrev DLogHardness {n : Nat} {G : Type} [AddCommGroup G] (P : Params n G) : Prop :=
  PedersenAssumptions.DLogHardness P

/-- Named computational-hiding surface attached to a concrete Pedersen
parameter instance. -/
abbrev ComputationalHiding {n : Nat} {G : Type} [AddCommGroup G] (P : Params n G) : Prop :=
  PedersenAssumptions.ComputationalHiding P n

/-- Named reduction surface connecting a hiding adversary against the Pedersen
instance `P` to a DLOG adversary against the same parameter family. -/
abbrev DLogReductionStatement {n : Nat} {G : Type} [AddCommGroup G] (P : Params n G) : Prop :=
  Nonempty (PedersenAssumptions.DLogReductionStatement P n)

/-- The current Pedersen-style interface exposes a single group element as the
commitment and reveals the full opening witness `(v, r)` to check openings. -/
def scheme {n : Nat} {G : Type} [AddCommGroup G]
    (P : Params n G) : Vec.Scheme :=
  { Idx := Fin n
    Val := Int
    Com := G
    Proof := (Fin n → Int) × Int
    Rand := Int
    commit := pedersenCommit P
    openAt := fun v r _ => (v, r)
    verifyAt := fun c i y π => pedersenCommit P π.1 π.2 = c ∧ π.1 i = y }

theorem openCorrect
    {n : Nat} {G : Type} [AddCommGroup G]
    (P : Params n G) :
    Vec.Scheme.OpenCorrect (scheme P) := by
  intro v r i
  simp [scheme]

theorem openSound_of_binding
    {n : Nat} {G : Type} [AddCommGroup G]
    (P : Params n G) (hBind : Binding P) :
    Vec.Scheme.OpenSound (scheme P) := by
  intro v r i y π h
  have h' : pedersenCommit P π.1 π.2 = pedersenCommit P v r ∧ π.1 i = y := by
    simpa [scheme] using h
  rcases h' with ⟨hCommit, hValue⟩
  have hEq : π = (v, r) := hBind hCommit
  have hVector : π.1 = v := congrArg Prod.fst hEq
  simpa [hVector] using hValue

/-- Canonical basis vector in `Fin n → Int`. -/
def basisGenerator {n : Nat} (j : Fin n) : Fin n → Int :=
  fun i => if i = j then 1 else 0

theorem basisExpansion
    {n : Nat} (v : Fin n → Int) :
    (∑ i, v i • basisGenerator i) = v := by
  funext j
  classical
  have hsum : (∑ i, (v i • basisGenerator i) j) = v j := by
    rw [Finset.sum_eq_single j]
    · simp [basisGenerator]
    · intro x _ hx
      have hx' : j ≠ x := by
        simpa [eq_comm] using hx
      simp [basisGenerator, Pi.smul_apply, hx']
    · simp [basisGenerator]
  simpa [Pi.smul_apply] using hsum

theorem pairBasisExpansion
    {n : Nat} (v : Fin n → Int) :
    (∑ i, (v i • basisGenerator i, (0 : Int))) = (v, 0) := by
  apply Prod.ext
  · have hfst : (∑ i, (v i • basisGenerator i, (0 : Int))).1 = ∑ i, v i • basisGenerator i := by
      simpa using (Prod.fst_sum (s := Finset.univ) (f := fun i => (v i • basisGenerator i, (0 : Int))))
    rw [hfst, basisExpansion]
  · have hsnd : (∑ i, (v i • basisGenerator i, (0 : Int))).2 = (0 : Int) := by
      simpa using (Prod.snd_sum (s := Finset.univ) (f := fun i => (v i • basisGenerator i, (0 : Int))))
    exact hsnd

/-- Blinding direction for the demo additive group. -/
def basisBlind {n : Nat} : (Fin n → Int) × Int :=
  (fun _ => 0, 1)

/-- Concrete demo parameters using the standard basis of `(Fin n → Int) × Int`. -/
def demoParams (n : Nat) : Params n ((Fin n → Int) × Int) where
  generators := fun i => (basisGenerator i, 0)
  blindingGenerator := basisBlind

theorem demo_commitVector_eq
    {n : Nat} (v : Fin n → Int) :
    commitVector (demoParams n) v = (v, 0) := by
  simpa [commitVector, demoParams] using pairBasisExpansion v

theorem demo_pedersenCommit_eq
    {n : Nat} (v : Fin n → Int) (r : Int) :
    pedersenCommit (demoParams n) v r = (v, r) := by
  rw [pedersenCommit, demo_commitVector_eq]
  ext j
  · simp [demoParams, basisBlind]
  · simp [demoParams, basisBlind]

theorem demo_binding (n : Nat) :
    Binding (demoParams n) := by
  intro vr₁ vr₂ h
  rcases vr₁ with ⟨v₁, r₁⟩
  rcases vr₂ with ⟨v₂, r₂⟩
  have hEq :
      (v₁, r₁) = (v₂, r₂) := by
    calc
      (v₁, r₁) = pedersenCommit (demoParams n) v₁ r₁ := (demo_pedersenCommit_eq v₁ r₁).symm
      _ = pedersenCommit (demoParams n) v₂ r₂ := h
      _ = (v₂, r₂) := demo_pedersenCommit_eq v₂ r₂
  simpa using hEq

theorem pedersenVerificationConsistencyAt
    {n : Nat} {G : Type} [AddCommGroup G]
    (P : Params n G) :
    Vec.Scheme.VerificationConsistencyAt (scheme P) := by
  exact Vec.Scheme.verificationConsistencyAt_of_openCorrect (scheme P) (openCorrect P)

theorem demo_verificationConsistencyAt (n : Nat) :
    Vec.Scheme.VerificationConsistencyAt (scheme (demoParams n)) := by
  exact pedersenVerificationConsistencyAt (demoParams n)

theorem demo_openCorrect (n : Nat) :
    Vec.Scheme.OpenCorrect (scheme (demoParams n)) :=
  openCorrect (demoParams n)

theorem demo_openSound (n : Nat) :
    Vec.Scheme.OpenSound (scheme (demoParams n)) :=
  openSound_of_binding (demoParams n) (demo_binding n)

theorem demo_commit_coordinates
    {n : Nat} (v : Fin n → Int) (r : Int) :
    (scheme (demoParams n)).commit v r = (v, r) := by
  calc
    (scheme (demoParams n)).commit v r = pedersenCommit (demoParams n) v r := by
      rfl
    _ = (v, r) := demo_pedersenCommit_eq v r

/-- Security-property bundle for Pedersen-style schemes at the current interface
level. `computationalHidingAt` is intentionally a named assumption surface, not
an automatically proved theorem. -/
def securityProps
    {n : Nat} {G : Type} [AddCommGroup G]
    (P : Params n G) :
    Vec.Scheme.SecurityProps (scheme P) where
  bindingAt := Binding P
  verificationConsistencyAt := Vec.Scheme.VerificationConsistencyAt (scheme P)
  computationalHidingAt := ComputationalHiding P
  extractable := False

/-- Under a named DLOG hardness witness and the corresponding classical
reduction statement, the Pedersen instance attached to `P` satisfies the
current computational-hiding surface. -/
theorem computationalHiding_of_dlogReduction
    {n : Nat} {G : Type} [AddCommGroup G]
    (P : Params n G)
    (hHard : DLogHardness P)
    (hRed : DLogReductionStatement P) :
    ComputationalHiding P := by
  rcases hRed with ⟨hRed'⟩
  exact PedersenAssumptions.computationalHiding_of_dlog hHard hRed'

/-- The `computationalHidingAt` field of `securityProps P` is discharged exactly
when the named DLOG hardness and reduction statements are supplied. -/
theorem computationalHiding_field_of_dlogReduction
    {n : Nat} {G : Type} [AddCommGroup G]
    (P : Params n G)
    (hHard : DLogHardness P)
    (hRed : DLogReductionStatement P) :
    (securityProps P).computationalHidingAt := by
  exact computationalHiding_of_dlogReduction P hHard hRed

def demoSecurityProps (n : Nat) :
    Vec.Scheme.SecurityProps (scheme (demoParams n)) where
  bindingAt := Binding (demoParams n)
  verificationConsistencyAt := Vec.Scheme.VerificationConsistencyAt (scheme (demoParams n))
  computationalHidingAt := False
  extractable := False

end IPAInstance
end Commit
end Crypto
end HeytingLean
