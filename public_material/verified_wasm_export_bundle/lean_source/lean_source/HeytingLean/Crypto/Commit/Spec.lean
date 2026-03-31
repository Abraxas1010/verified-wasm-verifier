import HeytingLean.Crypto.Commit
import HeytingLean.Crypto.Hash.Poseidon

/-
# Crypto.Commit.Spec

Abstract interfaces and specification-level properties for commitment
schemes. This module intentionally stays lightweight: it provides
structures and `Prop`-valued fields that other modules can instantiate
when they introduce concrete schemes (Pedersen, KZG, Merkle, etc.).
-/

namespace HeytingLean
namespace Crypto
namespace Commit
namespace Spec

/-- Generic (non-interactive) commitment scheme interface. -/
structure Scheme where
  Msg  : Type
  Rand : Type
  Com  : Type
  /-- Commitment function. -/
  commit : Msg → Rand → Com

namespace Scheme

/-- A canonical notion of a valid opening for a commitment in a scheme:
    the commitment is exactly `commit m r`. -/
def ValidOpening (S : Scheme) (c : S.Com) (m : S.Msg) (r : S.Rand) : Prop :=
  S.commit m r = c

/-- Correctness property for a commitment scheme: every output of
    `commit` admits a valid opening. -/
def Correct (S : Scheme) : Prop :=
  ∀ m r, ValidOpening S (S.commit m r) m r

/-- Abstract security properties:

* `hiding` can be instantiated by a cryptographic indistinguishability
  statement;
* `binding` by an infeasibility-of-finding-two-openings statement; and
* `collisionRes` by a collision-resistance statement when the scheme is
  derived from a hash family.

These are left as `Prop` fields so that different schemes can supply
their own formalizations over time. -/
structure SecurityProps (S : Scheme) where
  hidingProp       : Prop
  bindingProp      : Prop
  collisionResProp : Prop

theorem validOpening_self (S : Scheme) (m : S.Msg) (r : S.Rand) :
    ValidOpening S (S.commit m r) m r :=
  rfl

end Scheme

/-- Simple string-based commitment scheme instantiated by `commitString`.
    This is not intended to be cryptographically strong; it is provided
    as a convenient example and for use in CLIs and tests. -/
def StringScheme (domain : String) : Scheme :=
  { Msg := String
    , Rand := Unit
    , Com := String
    , commit := fun m _ => commitString domain m }

/-- The simple string-based scheme instantiated by `commitString` is
    correct: every commitment admits the obvious opening. -/
theorem StringScheme_correct (domain : String) :
    Scheme.Correct (StringScheme domain) := by
  intro m r
  -- In the string scheme, `Rand = Unit`, so the opening condition is
  -- simply reflexivity of `commit`.
  cases r
  rfl

/-! ## Polynomial-style commitment schemes (KZG-style interface)

This section provides an abstract interface for polynomial commitment
schemes in the spirit of Kate (KZG) commitments. It is deliberately
minimal: it does *not* fix any concrete representation of polynomials
or groups, and it phrases correctness and soundness as `Prop`-valued
properties to be instantiated by concrete schemes later.
-/

namespace Poly

/-- Abstract polynomial commitment scheme interface.

* `Poly` is the type of polynomials;
* `Point` is the type of evaluation points;
* `Value` is the type of evaluation results;
* `Com` is the type of commitments; and
* `Proof` is the type of evaluation proofs.

The scheme provides an abstract evaluation function `eval`, a
commitment function `commit`, and an evaluation-opening/verification
pair `openEval`/`verifyEval`. -/
structure Scheme where
  Poly  : Type
  Point : Type
  Value : Type
  Com   : Type
  Proof : Type
  /-- Abstract polynomial evaluation. -/
  eval       : Poly → Point → Value
  /-- Commit to a polynomial. -/
  commit     : Poly → Com
  /-- Produce a proof that a committed polynomial evaluates to
      `eval p x` at the point `x`. -/
  openEval   : Poly → Point → Proof
  /-- Verify that a commitment/proof pair opens to value `y` at
      the point `x`. -/
  verifyEval : Com → Point → Value → Proof → Prop

namespace Scheme

/-- Evaluation correctness: for every polynomial `p` and point `x`,
    if we commit to `p` and open at `x` using `openEval`, then
    verification succeeds for the exact value `eval p x`. -/
def EvalCorrect (S : Scheme) : Prop :=
  ∀ (p : S.Poly) (x : S.Point),
    let c := S.commit p
    let y := S.eval p x
    let π := S.openEval p x
    S.verifyEval c x y π

/-- Evaluation soundness: if an evaluation proof verifies against a
    commitment to `p`, then the claimed value `y` must equal the true
    evaluation `eval p x`. This is the core "no fake openings" property
    for KZG-style schemes. -/
def EvalSound (S : Scheme) : Prop :=
  ∀ (p : S.Poly) (x : S.Point) (y : S.Value) (π : S.Proof),
    S.verifyEval (S.commit p) x y π →
      S.eval p x = y

/-- Additional security properties (binding, hiding, extractability, etc.)
    specific to polynomial commitments can be packaged here. -/
structure SecurityProps (S : Scheme) where
  bindingEval  : Prop
  hidingEval   : Prop
  extractable  : Prop

end Scheme

/-! ### A minimal polynomial commitment scheme

This is a minimal, non-cryptographic instance of `Poly.Scheme` used to
exercise `EvalCorrect` and `EvalSound`. It treats the committed object
as the polynomial itself and uses direct evaluation equality as the
verification condition. -/

/-- Trivial polynomial commitment scheme where commitments are just the
    polynomials themselves and proofs are the claimed evaluation
    results. This is *not* intended to model any real cryptographic
    construction. -/
def demoScheme : Scheme :=
  { Poly  := Nat → Nat
    , Point := Nat
    , Value := Nat
    , Com   := Nat → Nat
    , Proof := Nat
    , eval := fun p x => p x
    , commit := fun p => p
    , openEval := fun p x => p x
    , verifyEval := fun c x y π => (π = y) ∧ (c x = y) }

/-- Evaluation correctness for `demoScheme`: by construction, opening at
    a point returns the true evaluation and verification checks this
    equality. -/
theorem demoScheme_evalCorrect : Scheme.EvalCorrect demoScheme := by
  intro p x
  -- Unfold the definition of `EvalCorrect` for `demoScheme`.
  simp [demoScheme]

/-- Evaluation soundness for `demoScheme`: any successful verification
    witness must equal the true evaluation. -/
theorem demoScheme_evalSound : Scheme.EvalSound demoScheme := by
  intro p x y π h
  -- From a successful verification we extract the equality
  -- `p x = y`, which is exactly the desired conclusion.
  have h' : (π = y) ∧ (p x = y) := by
    simpa [demoScheme] using h
  exact h'.right

end Poly

/-! ## Vector-style commitment schemes

An abstract interface for vector commitments, mirroring the polynomial
interface but phrased over index/value maps. As with the polynomial
layer, this is kept minimal and is intended to be instantiated by
concrete constructions later. -/

namespace Vec

/-- Abstract vector commitment scheme interface.

* `Idx` is the index type;
* `Val` is the value type;
* `Com` is the type of commitments; and
* `Proof` is the type of opening proofs. -/
structure Scheme where
  Idx   : Type
  Val   : Type
  Com   : Type
  Proof : Type
  Rand  : Type
  /-- Commit to a full index → value map. -/
  commit   : (Idx → Val) → Rand → Com
  /-- Produce an opening proof for index `i` in a given vector. -/
  openAt   : (Idx → Val) → Rand → Idx → Proof
  /-- Verify that a commitment/proof pair opens to value `y` at index
      `i`. -/
  verifyAt : Com → Idx → Val → Proof → Prop

namespace Scheme

/-- Opening correctness: for every vector `v` and index `i`, if we
    commit to `v` and open at `i` using `openAt`, then verification
    succeeds for the exact value `v i`. -/
def OpenCorrect (S : Scheme) : Prop :=
  ∀ (v : S.Idx → S.Val) (r : S.Rand) (i : S.Idx),
    let c := S.commit v r
    let y := v i
    let π := S.openAt v r i
    S.verifyAt c i y π

/-- Opening soundness: if an opening proof verifies against a
    commitment to `v` at index `i` with claimed value `y`, then `y`
    must equal the true value `v i`. -/
def OpenSound (S : Scheme) : Prop :=
  ∀ (v : S.Idx → S.Val) (r : S.Rand) (i : S.Idx) (y : S.Val) (π : S.Proof),
    S.verifyAt (S.commit v r) i y π →
      v i = y

/-- Canonical opening verification consistency at a position: if two vectors
agree at the opened index, then the canonical opening checks at that index are
observationally identical.

This is intentionally weaker than game-based cryptographic hiding. It is an
interface-level sanity condition for canonical openings, not a privacy theorem.
Schemes that want to claim real privacy should populate
`SecurityProps.computationalHidingAt` separately. -/
def VerificationConsistencyAt (S : Scheme) : Prop :=
  ∀ (v₁ v₂ : S.Idx → S.Val) (i : S.Idx),
    v₁ i = v₂ i →
    ∀ (r₁ r₂ : S.Rand),
      (S.verifyAt (S.commit v₁ r₁) i (v₁ i) (S.openAt v₁ r₁ i) ↔
        S.verifyAt (S.commit v₂ r₂) i (v₂ i) (S.openAt v₂ r₂ i))

/-- Any scheme with canonical opening correctness satisfies
`VerificationConsistencyAt`. -/
theorem verificationConsistencyAt_of_openCorrect (S : Scheme) (h : OpenCorrect S) :
    VerificationConsistencyAt S := by
  intro v₁ v₂ i _hEq r₁ r₂
  constructor <;> intro _h
  · exact h v₂ r₂ i
  · exact h v₁ r₁ i

/-- Additional security properties for vector commitments.

`verificationConsistencyAt` is the weak canonical-opening invariant above.
`computationalHidingAt` is reserved for an actual adversary-based privacy
statement once this subsystem grows the required oracle/game interface. -/
structure SecurityProps (S : Scheme) where
  bindingAt                 : Prop
  verificationConsistencyAt : Prop
  computationalHidingAt     : Prop
  extractable               : Prop

end Scheme

/-! ### A minimal vector commitment scheme

As with `Poly.demoScheme`, this is a trivial, non-cryptographic
instance that commits to the underlying vector directly and uses
equality-based verification. It is only intended for exercising
`OpenCorrect` and `OpenSound`. -/

/-- Trivial vector commitment scheme where commitments are just the
    underlying vectors and proofs are the claimed values. -/
def demoScheme : Scheme :=
  { Idx := Nat
    , Val := Nat
    , Com := Nat → Nat
    , Proof := Nat
    , Rand := Unit
    , commit := fun v _ => v
    , openAt := fun v _ i => v i
    , verifyAt := fun c i y π => (π = y) ∧ (c i = y) }

/-- Opening correctness for `demoScheme`: by construction, opening at an
    index returns the true value and verification checks this
    equality. -/
theorem demoScheme_openCorrect : Scheme.OpenCorrect demoScheme := by
  intro v r i
  cases r
  simp [demoScheme]

/-- Opening soundness for `demoScheme`: any successful verification
    witness must equal the true value at the opened index. -/
theorem demoScheme_openSound : Scheme.OpenSound demoScheme := by
  intro v r i y π h
  cases r
  have h' : (π = y) ∧ (v i = y) := by
    simpa [demoScheme] using h
  exact h'.right

end Vec

end Spec
end Commit
end Crypto
end HeytingLean
