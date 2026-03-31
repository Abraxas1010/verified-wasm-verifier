import HeytingLean.IteratedVirtual.Bridge.NucleusEnergy
import HeytingLean.IteratedVirtual.Bridge.MRClosure
import HeytingLean.IteratedVirtual.Bridge.MRSystemConnection
import HeytingLean.IteratedVirtual.Bridge.ModalCompanion
import HeytingLean.IteratedVirtual.Bridge.ModalSketch
import HeytingLean.IteratedVirtual.Bridge.HelixAdelic
import HeytingLean.IteratedVirtual.Bridge.HeytingConnection
import HeytingLean.IteratedVirtual.Pasting

/-!
# Tests.IteratedVirtual.ExtendedNoahSanity

Compile-only sanity checks for the “extended_noah” strict-only bridge pieces:
- nucleus/energy stability lemma,
- closure-system → nucleus bridge,
- modal syntax + Gödel translation utilities.
-/

namespace HeytingLean
namespace Tests
namespace IteratedVirtual

open HeytingLean.IteratedVirtual
open HeytingLean.IteratedVirtual.Bridge

-- Nucleus-energy bridge compiles and produces fixed-point statements.
example (t pitch : ℝ) (p : Point3R) :
    Bridge.NonnegNucleus.nonnegNucleus.R (Bridge.SpiralEnergy.energyWB t pitch p) =
      Bridge.SpiralEnergy.energyWB t pitch p :=
  Bridge.SpiralEnergy.energyWB_fixed (t := t) (pitch := pitch) (p := p)

-- Closure-system → nucleus bridge compiles.
section
  variable {X : Type} [SemilatticeInf X] [OrderBot X]
  variable (sys : Bridge.ClosureSystem X)
  variable (hExt : ∀ x, x ≤ sys.β x)
  variable (hMeet : ∀ x y, sys.β (x ⊓ y) = sys.β x ⊓ sys.β y)

  #check Bridge.ClosureSystem.toNucleus sys hExt hMeet
end

-- Modal syntax utilities compile.
example (φ : Bridge.ModalFormula) :
    0 < Bridge.modalDepth (Bridge.goedelTranslation φ) :=
  Bridge.modalDepth_goedelTranslation_pos φ

-- GMT correspondence is available (provability-level) via `Foundation`.
section
  open LO
  open LO.Entailment
  variable (φ : LO.Propositional.Formula ℕ)

  example : (LO.Propositional.Int ⊢ φ) ↔ (LO.Modal.S4 ⊢ φᵍ) :=
    Bridge.gmt_correspondence φ
end

-- Helix “adelic” decomposition compiles and has correct discrete periodicity under `step = 2π/n`.
example (pitch : ℝ) (n k : Nat) (hn : 0 < n) :
    let h : Bridge.HelixDecomposition := { step := (2 * Real.pi) / (n : ℝ), pitch := pitch }
    h.xy (k + n) = h.xy k := by
  intro h
  simpa using (Bridge.HelixDecomposition.local_periodic_of_step_eq_two_pi_div (h := h) n hn rfl k)

-- MR loop-closing operator is an idempotent projection (reusing `ClosingTheLoop.MR`).
section
  open HeytingLean.ClosingTheLoop
  universe u v
  variable {S : MR.MRSystem.{u, v}} {b : S.B} (RI : MR.RightInverseAt S b)
  variable (Φ : MR.Selector S)

  example :
      let p := Bridge.closeSelectorProjection (S := S) (b := b) RI
      p (p Φ) = p Φ := by
    intro p
    exact Bridge.IdemProjection.idem_apply p Φ
end

-- Nucleus-commuting maps preserve fixed points (generic “stability transport” lemma).
section
  open HeytingLean.Core
  universe u v
  variable {α : Type u} {β : Type v} [SemilatticeInf α] [OrderBot α] [SemilatticeInf β] [OrderBot β]
  variable (Nα : Nucleus α) (Nβ : Nucleus β) (f : Bridge.NucleusHom (α := α) (β := β) Nα Nβ)
  variable (a : α) (ha : Nα.R a = a)

  example : Nβ.R (f a) = f a :=
    Bridge.fixedPoint_map (f := f) ha
end

-- “Virtual cell” pasting coherence (substitution associativity) compiles.
section
  open HeytingLean.IteratedVirtual
  universe u v w
  variable (V : VirtualDoubleCategory.{u, v, w})
  variable {a b : V.Obj} (f : V.Horiz a b)
  variable (p : Pasting (V := V) f)
  variable (σ τ : ∀ {x y : V.Obj}, (g : V.Horiz x y) → Pasting (V := V) g)

  example :
      Pasting.bind (V := V) (Pasting.bind (V := V) p σ) τ =
        Pasting.bind (V := V) p (fun g => Pasting.bind (V := V) (σ g) τ) :=
    Pasting.bind_assoc (V := V) p σ τ
end

end IteratedVirtual
end Tests
end HeytingLean
