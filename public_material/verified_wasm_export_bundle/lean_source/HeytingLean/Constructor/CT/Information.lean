import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Basic
import HeytingLean.Constructor.Core
import HeytingLean.Constructor.CT.Core
import HeytingLean.Constructor.CT.Nucleus

/-
# Constructor Theory of information (CT information media)

Minimal scaffolding for information media in Constructor Theory:
* `InfoVariable` marks CT variables that support permutation and copy tasks
  which are CT‑possible under a given CT nucleus;
* `Interop` packages the interoperability principle for a pair of
  information variables and a chosen product CT nucleus;
* small classical examples over `Bool` using the trivial CT nucleus;
* a thin helper that exposes `Constructor.Meta.interoperability` in a
  convenient form for ambient lattices.
-/

namespace HeytingLean
namespace Constructor
namespace CT

open Classical

universe u v w

variable {σ : Type u}

/-- A CT information variable over a substrate `σ` for a fixed CT nucleus
`J`.  Besides the underlying CT `Variable`, it records:
* an abstract type `Perm` of permutation codes;
* for each permutation code, a task realising the permutation;
* a copy task; and
* proofs that all these tasks are CT‑possible under `J`.

Concrete substrates are expected to give these fields more structure; here
they serve as lightweight markers that permutations and copying are
realised at the task level. -/
structure InfoVariable (σ : Type u) (J : CTNucleus σ) extends Variable σ where
  /-- Abstract type of permutation codes for this variable. -/
  Perm : Type v
  /-- CT task implementing a permutation. -/
  permTask : Perm → Task σ
  /-- Every permutation task is CT‑possible under `J`. -/
  perm_possible :
    ∀ p : Perm, CTNucleus.possible (J := J) (permTask p)
  /-- CT task implementing copying of the variable. -/
  copyTask : Task σ
  /-- Copying is CT‑possible under `J`. -/
  copy_possible :
    CTNucleus.possible (J := J) copyTask

/-- Interoperability witness for a pair of CT information variables:
given CT nuclei `Jσ`, `Jτ` and a product nucleus `Jprod`, packaging an
information variable on `σ × τ`.

Concrete substrates are expected to construct values of this structure. -/
structure Interop
    {σ τ : Type u}
    (Jσ : CTNucleus σ) (Jτ : CTNucleus τ) (Jprod : CTNucleus (σ × τ))
    (X : InfoVariable σ Jσ) (Y : InfoVariable τ Jτ) where
  /-- Information variable on the product substrate. -/
  product_info : InfoVariable (σ × τ) Jprod

namespace Examples

open CT
open CT.Examples
open CTNucleus

/-- A tiny information variable over `Bool` for the trivial CT nucleus.

This uses the empty CT variable on `Bool` as a base and records a single
permutation/copy task (both reusing `swapTaskBool`).  Under the trivial
CT nucleus, all such tasks are CT‑possible. -/
def boolInfoVariable :
    InfoVariable Bool (trivial (σ := Bool)) where
  toVariable := emptyVariable Bool
  Perm := Unit
  permTask _ := swapTaskBool
  perm_possible _ :=
    trivial_possible (σ := Bool) (T := swapTaskBool)
  copyTask := swapTaskBool
  copy_possible :=
    trivial_possible (σ := Bool) (T := swapTaskBool)

/-- Interoperability example: the product of two `Bool` information
variables (for the trivial CT nucleus) is again an information variable
over `Bool × Bool` for the trivial product nucleus. -/
def boolInterop :
    Interop
      (Jσ := trivial (σ := Bool))
      (Jτ := trivial (σ := Bool))
      (Jprod := trivial (σ := Bool × Bool))
      boolInfoVariable
      boolInfoVariable where
  product_info :=
    { toVariable := emptyVariable (Bool × Bool)
      Perm := Unit
      permTask _ := { arcs := [] }
      perm_possible _ :=
        trivial_possible (σ := Bool × Bool)
          (T := { arcs := [] })
      copyTask := { arcs := [] }
      copy_possible :=
        trivial_possible (σ := Bool × Bool)
          (T := { arcs := [] }) }

end Examples

/-! ### Adapter helper towards `Constructor.Meta`

Substrate‑specific CT adapters are expected to map CT information media
into ambient lattices `α` equipped with a nucleus `R` and a
`Constructor.Meta R` instance.  The lemma below is a small wrapper
around `Meta.interoperability` that such adapters can reuse once they
have produced ambient elements marked as information variables. -/

namespace ToMeta

variable {α : Type w} [CompleteLattice α]
variable (R : Nucleus α) [Constructor.Meta R]

/-- If two ambient elements are marked as information variables for the
meta‑theoretic nucleus `R`, then their conjunction is also an information
variable and remains globally possible. -/
lemma interop_from_meta {x y : α}
    (hx : Constructor.Meta.isInfoVariable (R := R) x)
    (hy : Constructor.Meta.isInfoVariable (R := R) y) :
    Constructor.Meta.isInfoVariable (R := R) (x ⊓ y) ∧
      Constructor.possible R (x ⊓ y) :=
  Constructor.Meta.interoperability (R := R) hx hy

end ToMeta

end CT
end Constructor
end HeytingLean
