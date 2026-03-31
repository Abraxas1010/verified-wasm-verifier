import Mathlib.Data.Set.Lattice
import Mathlib.Order.Nucleus
import Mathlib.Order.Sublocale
import Mathlib.Order.Heyting.Basic
import HeytingLean.Constructor.CT.Core

/-
# Constructor Theory nucleus on tasks

Abstract CT nucleus on sets of tasks over a fixed substrate `σ`.  This
captures the closure properties of Constructor Theory at the level of
task‑sets, independently of any particular physical model.

Key components:
* `CTNucleus` : interior‑style operator `J` on `Set (Task σ)`;
* `possible`  : CT possibility predicate for individual tasks;
* basic lemmas: inflation, idempotence, and monotonicity of `J`.

Concrete substrates are expected to provide instances of `CTNucleus` and
connect `possible` to the generic `Constructor.possible` predicate from
`HeytingLean.Constructor.Core`.
-/

namespace HeytingLean
namespace Constructor
namespace CT

open Classical
open Set

universe u v

variable {σ : Type u}

/-- CT nucleus on sets of tasks over a substrate `σ`.

The operator `J` is an interior‑style operator (inflationary, idempotent,
and meet‑preserving via `inter`) that is additionally closed under the
basic syntactic task constructors `Task.seq` and `Task.par`. -/
structure CTNucleus (σ : Type u) where
  /-- Interior‑style operator on sets of tasks. -/
  J : Set (Task σ) → Set (Task σ)
  /-- Inflation: every set is contained in its CT closure. -/
  infl : ∀ X, X ⊆ J X
  /-- Monotonicity: enlarging the input set cannot shrink its CT closure. -/
  mono : ∀ {X Y}, X ⊆ Y → J X ⊆ J Y
  /-- Idempotence: `J` is an interior operator. -/
  idem : ∀ X, J (J X) = J X
  /-- Meet preservation: closure of an intersection equals the intersection
  of the closures. -/
  inter : ∀ X Y, J (X ∩ Y) = (J X) ∩ (J Y)
  /-- Closure under serial composition of tasks. -/
  closed_seq :
    ∀ {X} {T U : Task σ},
      T ∈ J X → U ∈ J X → Task.seq T U ∈ J X
  /-- Closure under parallel composition of tasks. -/
  closed_par :
    ∀ {X} {T U : Task σ},
      T ∈ J X → U ∈ J X → Task.par T U ∈ J X

/-- View a `CTNucleus` as a Mathlib nucleus on the powerset lattice of
tasks.  This packages the closure behaviour into a standard `Nucleus`
value that can be used with generic sublocale / Heyting machinery. -/
def CTNucleus.toNucleus (J : CTNucleus σ) : Nucleus (Set (Task σ)) where
  toFun := J.J
  map_inf' := by
    intro X Y
    -- On `Set`, `⊓` is intersection, so we can reuse `inter`.
    simp [Set.inf_eq_inter, J.inter]
  idempotent' := by
    intro X
    -- From equality to `≤` via `le_rfl`.
    simp [J.idem X]
  le_apply' := by
    intro X
    exact J.infl X

namespace CTNucleus

variable (J : CTNucleus σ)

/-- A task is CT‑possible when it lies in the CT closure of the singleton
set containing it. -/
def possible (T : Task σ) : Prop :=
  T ∈ J.J {T}

/-- A task is CT‑impossible when it is not CT‑possible. -/
def impossible (T : Task σ) : Prop :=
  ¬ possible (J := J) T

@[simp] theorem infl_sub (X : Set (Task σ)) :
    X ⊆ J.J X :=
  J.infl X

@[simp] theorem idempotent (X : Set (Task σ)) :
    J.J (J.J X) = J.J X :=
  J.idem X

/-- Monotonicity of `J` as a convenience lemma. -/
theorem mono' {X Y : Set (Task σ)} (hXY : X ⊆ Y) :
    J.J X ⊆ J.J Y :=
  J.mono hXY

end CTNucleus

/-- Fixed points of a CT nucleus, viewed as a sublocale of the powerset
of tasks.  This mirrors `LoF.Reentry.Omega` but specialised to CT. -/
abbrev Omega (J : CTNucleus σ) : Type u :=
  (CTNucleus.toNucleus (σ := σ) J).toSublocale

namespace Omega

variable (J : CTNucleus σ)

instance instHeytingOmega : HeytingAlgebra (Omega (σ := σ) J) :=
  inferInstance

end Omega

namespace Examples

/-- Trivial CT nucleus that declares every task possible by sending any
set of tasks to `Set.univ`.  This is mainly useful as a very small
sanity‑check instance. -/
def trivial (σ : Type u) : CTNucleus σ where
  J := fun _ => (Set.univ : Set (Task σ))
  infl := by
    intro X T hXT
    simp
  mono := by
    intro X Y hXY T hJT
    simp
  idem := by
    intro X
    ext T
    simp
  inter := by
    intro X Y
    ext T
    simp
  closed_seq := by
    intro X T U hT hU
    simp
  closed_par := by
    intro X T U hT hU
    simp

/-- Under the trivial CT nucleus, every task is CT‑possible. -/
theorem trivial_possible {σ : Type u} (T : Task σ) :
    CTNucleus.possible (J := trivial (σ := σ)) T := by
  unfold CTNucleus.possible
  simp [trivial]

end Examples

/-! ### Heyting-style residuation on CT fixed points

The fixed points `Ω_{J_CT}` of any CT nucleus carry a Heyting algebra
structure via the generic sublocale construction.  As a convenience we
restate the standard Heyting adjunction in this setting.
-/

namespace Heyting

variable (J : CTNucleus σ)

/-- Heyting-style adjunction on the CT fixed-point algebra `Ω_{J_CT}`:
`a ⊓ b ≤ c` iff `b ≤ a ⇨ c`.  This is a direct restatement of the
standard Heyting adjunction on the sublocale associated to the nucleus
`J.toNucleus`. -/
lemma residuation (A B C : Omega (σ := σ) J) :
    A ⊓ B ≤ C ↔ B ≤ (A ⇨ C) := by
  -- This is exactly the generic Heyting adjunction `le_himp_iff`, up to
  -- commutativity of `⊓`.
  have h :
      B ≤ (A ⇨ C) ↔ B ⊓ A ≤ C :=
    (GeneralizedHeytingAlgebra.le_himp_iff (a := B) (b := A) (c := C))
  have h' :
      B ≤ (A ⇨ C) ↔ A ⊓ B ≤ C := by
    simp [h, inf_comm]
  exact h'.symm

end Heyting

/-! ### CT dial (θ_CT)

For now this is an abstract measure from tasks to an extended natural
number.  Concrete substrates may refine this with a constructor-depth
metric or birth index. -/

def thetaCT (_J : CTNucleus σ) (_T : Task σ) : WithTop Nat :=
  (⊤ : WithTop Nat)

end CT
end Constructor
end HeytingLean
