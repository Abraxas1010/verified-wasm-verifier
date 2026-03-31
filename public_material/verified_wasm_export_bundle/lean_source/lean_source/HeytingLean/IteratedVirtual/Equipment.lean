import HeytingLean.IteratedVirtual.Basic

/-!
# IteratedVirtual.Equipment

Adds “companions” and “conjoints” (as data) to a `VirtualDoubleCategory`, giving a
first-pass notion of “virtual equipment” / “framed bicategory” scaffolding.

We intentionally do **not** impose coherence laws yet; the goal is a stable API
surface that compiles and can be instantiated.
-/

namespace HeytingLean
namespace IteratedVirtual

universe u v w

open CategoryTheory

/-- A (virtual) equipment: companions and conjoints for every vertical arrow, plus the
unit/counit multi-cells witnessing them (as data, no laws yet). -/
structure VirtualEquipment extends VirtualDoubleCategory.{u, v, w} where
  companion : ∀ {a b : Obj}, (a ⟶ b) → Horiz a b
  conjoint : ∀ {a b : Obj}, (a ⟶ b) → Horiz b a

  /-- The companion unit: `idₕ a ⇒ companion f` with vertical frame `𝟙 a, f`. -/
  companionUnit : ∀ {a b : Obj} (f : a ⟶ b),
      Cell (n := 1)
        (A := fin2 a a)
        (B := fin2 a b)
        (v := fun i =>
          match i with
          | ⟨0, _⟩ => 𝟙 a
          | ⟨1, _⟩ => f)
        (h := fun i =>
          match i with
          | ⟨0, _⟩ => by
              simpa [fin2] using (horizId a))
        (tgt := companion f)

  /-- The companion counit: `companion f ⇒ idₕ b` with vertical frame `f, 𝟙 b`. -/
  companionCounit : ∀ {a b : Obj} (f : a ⟶ b),
      Cell (n := 1)
        (A := fin2 a b)
        (B := fin2 b b)
        (v := fun i =>
          match i with
          | ⟨0, _⟩ => f
          | ⟨1, _⟩ => 𝟙 b)
        (h := fun i =>
          match i with
          | ⟨0, _⟩ => by
              simpa [fin2] using (companion f))
        (tgt := horizId b)

  /-- The conjoint unit: `idₕ a ⇒ conjoint f` with vertical frame `f, 𝟙 a`. -/
  conjointUnit : ∀ {a b : Obj} (f : a ⟶ b),
      Cell (n := 1)
        (A := fin2 a a)
        (B := fin2 b a)
        (v := fun i =>
          match i with
          | ⟨0, _⟩ => f
          | ⟨1, _⟩ => 𝟙 a)
        (h := fun i =>
          match i with
          | ⟨0, _⟩ => by
              simpa [fin2] using (horizId a))
        (tgt := conjoint f)

  /-- The conjoint counit: `conjoint f ⇒ idₕ b` with vertical frame `𝟙 b, f`. -/
  conjointCounit : ∀ {a b : Obj} (f : a ⟶ b),
      Cell (n := 1)
        (A := fin2 b a)
        (B := fin2 b b)
        (v := fun i =>
          match i with
          | ⟨0, _⟩ => 𝟙 b
          | ⟨1, _⟩ => f)
        (h := fun i =>
          match i with
          | ⟨0, _⟩ => by
              simpa [fin2] using (conjoint f))
        (tgt := horizId b)

end IteratedVirtual
end HeytingLean
