import HeytingLean.Util.VirtualChain
import HeytingLean.Crypto.Lattice.Reductions

/-!
# Crypto.Lattice.VirtualReductionChain

Systematic “virtualization via chains” for statement-level lattice reductions.

`Reduction V₁ V₂` already has a true composition operation (`Reduction.comp`), but in practice it is
often useful to keep an explicit **audit trail** of intermediate reductions while still being able
to “compile” the chain into one composed reduction when needed.

Since `Reduction` is *heterogeneous* in the secret type, we package recovery views as a sigma type.
-/

namespace HeytingLean
namespace Crypto
namespace Lattice

open HeytingLean.Util

universe u

/-- A heterogeneous recovery view (packages the secret type). -/
abbrev AnyRecoveryView : Type (u + 1) :=
  Σ S : Type u, RecoveryView S

/-- A heterogeneous reduction between heterogeneous recovery views. -/
structure AnyReduction (V W : AnyRecoveryView.{u}) : Type (u + 1) where
  red : Reduction V.2 W.2

namespace AnyReduction

def id (V : AnyRecoveryView.{u}) : AnyReduction V V :=
  ⟨Reduction.id V.2⟩

def comp {V W U : AnyRecoveryView.{u}} (R₁ : AnyReduction V W) (R₂ : AnyReduction W U) : AnyReduction V U :=
  ⟨Reduction.comp R₁.red R₂.red⟩

end AnyReduction

namespace AnyReductionChain

/-- A chain of reductions with explicit intermediate views. -/
abbrev Chain (V W : AnyRecoveryView.{u}) :=
  VirtualChain AnyReduction V W

def compile {V W : AnyRecoveryView.{u}} : Chain V W → AnyReduction V W
  | .nil V => AnyReduction.id V
  | .cons r rest => AnyReduction.comp r (compile rest)

def unsolvable (V : AnyRecoveryView.{u}) : Prop :=
  ¬ ∃ recover : V.2.Pub → V.1, RecoveryView.solves V.2 recover

theorem unsolvable_of_unsolvable {V W : AnyRecoveryView.{u}} (p : Chain V W) :
    unsolvable W → unsolvable V := by
  intro hW hV
  have h := Reduction.unsolvable_of_unsolvable (R := (compile p).red)
  exact h hW hV

end AnyReductionChain

end Lattice
end Crypto
end HeytingLean
