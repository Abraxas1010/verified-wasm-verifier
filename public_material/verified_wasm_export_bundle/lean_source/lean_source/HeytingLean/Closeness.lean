import HeytingLean.Quantum.Translate.Modality
import HeytingLean.Quantum.Translate.Omega

/-
  HeytingLean.Closeness

  Ω_R-oriented closeness primitives specialized to the fixed-point
  sublocale `Omega M` of a modality `M` (a nucleus on a Heyting algebra).
  We provide a monotone measure on `Omega M` and derived distances:
    - dPlusΩ A B := μ (A ⇒R B) using `Omega.imp`
    - dSymΩ  A B := max (dPlusΩ A B) (dPlusΩ B A)
    - gapΩ   A B := (A ⊓ ¬R B) ⊔ (B ⊓ ¬R A) using `Omega.inf/sup` and neg via `⇒ ⊥`
-/

namespace HeytingLean
namespace Closeness

open scoped Classical
open HeytingLean.Quantum.Translate

universe u

-- A monotone measure on the Ω_R carrier `Omega M`.
structure OmegaMeasure {α : Type u}
    [Order.Frame α] [HeytingAlgebra α]
    (M : Modality α) where
  μ     : Omega M → Nat
  mono  : ∀ {a b : Omega M}, a ≤ b → μ a ≤ μ b
  μ_top : μ (Omega.top (M := M)) = 0

variable {α : Type u} [Order.Frame α] [HeytingAlgebra α]
variable (M : Modality α)
variable (Me : OmegaMeasure (M := M))

-- Heyting negation on Ω_R: ¬R x := x ⇒R ⊥
def negΩ (x : Omega M) : Omega M :=
  Omega.imp (M := M) x (Omega.bot (M := M))

-- Directional residuation distance on Ω_R
def dPlusΩ (A B : Omega M) : Nat :=
  Me.μ (Omega.imp (M := M) A B)

-- Symmetric hemimetric
def dSymΩ (A B : Omega M) : Nat :=
  Nat.max (dPlusΩ (M := M) (Me := Me) A B) (dPlusΩ (M := M) (Me := Me) B A)

-- Closed symmetric difference on Ω_R
def gapΩ (A B : Omega M) : Omega M :=
  let nA := negΩ (M := M) A
  let nB := negΩ (M := M) B
  Omega.sup (M := M) (Omega.inf (M := M) A nB) (Omega.inf (M := M) B nA)

def dGapΩ (A B : Omega M) : Nat :=
  Me.μ (gapΩ (M := M) A B)

-- Trivial zero measure (useful for smoke tests and CLI bootstrapping)
def zeroOmegaMeasure (M : Modality α) : OmegaMeasure (M := M) where
  μ     := fun _ => 0
  mono  := by intro a b _; exact Nat.le_refl 0
  μ_top := rfl

/-- A simple idempotent-birth measure for any modality: 0 for closed points,
    1 otherwise. Since `Omega M` contains only closed points, this reduces to 0,
    but the definition is useful documentation and matches the intended
    “steps-to-stabilize” semantics. -/
def ibirthMeasure (M : Modality α) : OmegaMeasure (M := M) :=
  zeroOmegaMeasure (M := M)

/-- IR-footprint measure: currently the constant-0 measure, kept as a small
    baseline for smoke tests and CLI bootstrapping. -/
def irFootprintMeasure (M : Modality α) : OmegaMeasure (M := M) :=
  zeroOmegaMeasure (M := M)

/-! ### Basic invariants for the Ω-distance scaffold

The current `OmegaMeasure` abstraction only requires monotonicity and
`μ ⊤ = 0`.  From these hypotheses alone we can already prove that all
derived distances are pointwise bounded by `0`, hence are identically
`0` as natural numbers.

These lemmas make the latent invariants in the documentation explicit:

* for any Ω-points `A, B`, `dPlusΩ A B = 0` and `dSymΩ A B = 0`,
* similarly, `dGapΩ A B = 0` for all `A, B`.

In particular, the “soundness” and “monotonicity” constraints recorded
in the latent audit plan hold outright for the current scaffold.  A
future, more refined `OmegaMeasure` (backed by a nontrivial birth or
resource index) will necessarily relax or change the `μ_top = 0`
assumption; at that point these lemmas would be revisited and upgraded
to genuinely informative inequalities.
-/

lemma dPlusΩ_le_zero (A B : Omega M) :
    dPlusΩ (M := M) (Me := Me) A B ≤ 0 := by
  -- `A ⇒R B` is always ≤ ⊤, so monotonicity gives a bound by `μ_top = 0`.
  have hle : Omega.imp (M := M) A B ≤ Omega.top (M := M) :=
    le_top
  have hμ := Me.mono hle
  simpa [dPlusΩ, Me.μ_top] using hμ

lemma dPlusΩ_eq_zero (A B : Omega M) :
    dPlusΩ (M := M) (Me := Me) A B = 0 := by
  -- A natural number bounded above by `0` must be `0`.
  apply Nat.le_antisymm
  · exact dPlusΩ_le_zero (M := M) (Me := Me) A B
  · exact Nat.zero_le _

lemma dSymΩ_eq_zero (A B : Omega M) :
    dSymΩ (M := M) (Me := Me) A B = 0 := by
  -- Both directional components are zero, so the max is zero.
  have h1 : dPlusΩ (M := M) (Me := Me) A B = 0 := dPlusΩ_eq_zero (M := M) (Me := Me) A B
  have h2 : dPlusΩ (M := M) (Me := Me) B A = 0 := dPlusΩ_eq_zero (M := M) (Me := Me) B A
  simp [dSymΩ, h1, h2]

lemma dGapΩ_le_zero (A B : Omega M) :
    dGapΩ (M := M) (Me := Me) A B ≤ 0 := by
  -- `gapΩ A B ≤ ⊤` for any `A,B`, so the same monotonicity argument applies.
  have hle : gapΩ (M := M) A B ≤ Omega.top (M := M) :=
    le_top
  have hμ := Me.mono hle
  simpa [dGapΩ, Me.μ_top] using hμ

lemma dGapΩ_eq_zero (A B : Omega M) :
    dGapΩ (M := M) (Me := Me) A B = 0 := by
  apply Nat.le_antisymm
  · exact dGapΩ_le_zero (M := M) (Me := Me) A B
  · exact Nat.zero_le _

/-! ### Lens invariance (scaffold)

We record a basic invariance lemma for the identity lens; nontrivial lens
invariance across transports (Tensor/Graph/Clifford) will be added when the
explicit enc/dec maps are exposed at this module boundary.
-/

@[simp] lemma dSymΩ_id_invariant (A B : Omega M) :
    dSymΩ (M := M) (Me := Me) A B = dSymΩ (M := M) (Me := Me) A B := rfl

end Closeness
end HeytingLean
