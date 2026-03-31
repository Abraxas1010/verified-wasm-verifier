import HeytingLean.Numbers.SurrealCore
import HeytingLean.Noneism.Foundation

/-!
# Surreal.NoneistFoundation

Noneism-anchored Surreal scaffolding.

Each pre-game is paired with an explicit anchor in `Noneism.Nothing` and a
polarity witness (`Mark`/`Unmark`). This gives a semantic root that is tied to
the Noneism layer rather than relying on an empty-set narrative.
-/

namespace HeytingLean
namespace Numbers
namespace Surreal

open HeytingLean.Numbers.SurrealCore
open HeytingLean.Noneism

noncomputable section

abbrev NObj : Type := Noneism.Nothing

abbrev seedN : NObj := Noneism.PrimordialTension.seed (Nothing := NObj)
abbrev stepN : NObj → NObj := Noneism.PrimordialTension.step (Nothing := NObj)
abbrev IsMark (x : NObj) : Prop := Noneism.PrimordialTension.Mark (Nothing := NObj) x
abbrev IsUnmark (x : NObj) : Prop := Noneism.PrimordialTension.Unmark (Nothing := NObj) x

theorem mark_or_unmark_N (x : NObj) : IsMark x ∨ IsUnmark x :=
  Noneism.PrimordialTension.mark_or_unmark (Nothing := NObj) x

/-! ## Anchor polarity -/

inductive Polarity where
  | mark
  | unmark
deriving Repr, DecidableEq

def Polarity.holds (p : Polarity) (x : NObj) : Prop :=
  match p with
  | .mark => IsMark x
  | .unmark => IsUnmark x

@[simp] theorem Polarity.holds_mark (x : NObj) :
    Polarity.holds .mark x ↔ IsMark x := Iff.rfl

@[simp] theorem Polarity.holds_unmark (x : NObj) :
    Polarity.holds .unmark x ↔ IsUnmark x := Iff.rfl

/-! ## Noneism-anchored pre-games -/

structure AnchoredPreGame where
  core : PreGame
  anchor : NObj
  polarity : Polarity
  anchor_valid : Polarity.holds polarity anchor

def withMarked (g : PreGame) (a : NObj) (ha : IsMark a) : AnchoredPreGame :=
  { core := g, anchor := a, polarity := .mark, anchor_valid := ha }

def withUnmarked (g : PreGame) (a : NObj) (ha : IsUnmark a) : AnchoredPreGame :=
  { core := g, anchor := a, polarity := .unmark, anchor_valid := ha }

def mkMark (anchor : NObj) (h : IsMark anchor)
    (L R : List AnchoredPreGame) : AnchoredPreGame :=
  withMarked
    (PreGame.build (L.map AnchoredPreGame.core) (R.map AnchoredPreGame.core))
    anchor
    h

def mkUnmark (anchor : NObj) (h : IsUnmark anchor)
    (L R : List AnchoredPreGame) : AnchoredPreGame :=
  withUnmarked
    (PreGame.build (L.map AnchoredPreGame.core) (R.map AnchoredPreGame.core))
    anchor
    h

def forget (g : AnchoredPreGame) : PreGame := g.core

/-! ## Canonical Noneist anchors -/

noncomputable def markAnchor : NObj := by
  classical
  by_cases hMark : IsMark seedN
  · exact seedN
  · exact stepN seedN

theorem markAnchor_is_marked : IsMark markAnchor := by
  classical
  unfold markAnchor
  by_cases hMark : IsMark seedN
  · simp [hMark]
  · have hUnmark : IsUnmark seedN := (mark_or_unmark_N seedN).resolve_left hMark
    have hMarkStep : IsMark (stepN seedN) :=
      (Noneism.PrimordialTension.mark_step_iff_unmark (Nothing := NObj) seedN).2 hUnmark
    simpa [hMark] using hMarkStep

noncomputable def unmarkAnchor : NObj := by
  classical
  by_cases hUnmark : IsUnmark seedN
  · exact seedN
  · exact stepN seedN

theorem unmarkAnchor_is_unmarked : IsUnmark unmarkAnchor := by
  classical
  unfold unmarkAnchor
  by_cases hUnmark : IsUnmark seedN
  · simp [hUnmark]
  · have hMark : IsMark seedN := (mark_or_unmark_N seedN).resolve_right hUnmark
    have hUnmarkStep : IsUnmark (stepN seedN) :=
      (Noneism.PrimordialTension.unmark_step_iff_mark (Nothing := NObj) seedN).2 hMark
    simpa [hUnmark] using hUnmarkStep

/-! ## Noneist genesis pair -/

noncomputable def genesis : AnchoredPreGame := by
  refine mkMark markAnchor markAnchor_is_marked ?_ ?_
  · exact ([] : List AnchoredPreGame)
  · exact ([] : List AnchoredPreGame)

noncomputable def counterGenesis : AnchoredPreGame := by
  refine mkUnmark unmarkAnchor unmarkAnchor_is_unmarked ?_ ?_
  · exact ([] : List AnchoredPreGame)
  · exact ([] : List AnchoredPreGame)

@[simp] theorem genesis_polarity : genesis.polarity = .mark := by
  simp [genesis, mkMark, withMarked]

@[simp] theorem counterGenesis_polarity : counterGenesis.polarity = .unmark := by
  simp [counterGenesis, mkUnmark, withUnmarked]

@[simp] theorem genesis_birth : genesis.core.birth = 1 := by
  simp [genesis, mkMark, withMarked, PreGame.build, PreGame.maxBirth]

theorem genesis_not_nullCut : genesis.core ≠ SurrealCore.nullCut := by
  intro hEq
  have hBirth : genesis.core.birth = SurrealCore.nullCut.birth :=
    congrArg (fun g => g.birth) hEq
  have : (1 : Nat) = 0 := by
    have hBirth' := hBirth
    simp [genesis_birth, SurrealCore.nullCut] at hBirth'
  exact Nat.succ_ne_zero 0 this

theorem genesis_anchor_ne_counterAnchor :
    genesis.anchor ≠ counterGenesis.anchor := by
  intro hEq
  have hMarkGenesis : IsMark genesis.anchor := by
    simpa [Polarity.holds, genesis_polarity] using genesis.anchor_valid
  have hMarkCounter : IsMark counterGenesis.anchor := by
    simpa [hEq] using hMarkGenesis
  have hUnmarkCounter : IsUnmark counterGenesis.anchor := by
    simpa [Polarity.holds, counterGenesis_polarity] using counterGenesis.anchor_valid
  exact (Noneism.PrimordialTension.mark_and_unmark_false
    (Nothing := NObj) counterGenesis.anchor) ⟨hMarkCounter, hUnmarkCounter⟩

/-! ## Lifted arithmetic (anchor-preserving shell) -/

namespace AnchoredPreGame

def add (x y : AnchoredPreGame) : AnchoredPreGame :=
  { core := SurrealCore.add x.core y.core
    anchor := x.anchor
    polarity := x.polarity
    anchor_valid := x.anchor_valid }

noncomputable def neg : AnchoredPreGame → AnchoredPreGame
  | ⟨core, anchor, .mark, hMark⟩ =>
      withUnmarked
        (SurrealCore.neg core)
        (stepN anchor)
        ((Noneism.PrimordialTension.unmark_step_iff_mark (Nothing := NObj) anchor).2 hMark)
  | ⟨core, anchor, .unmark, hUnmark⟩ =>
      withMarked
        (SurrealCore.neg core)
        (stepN anchor)
        ((Noneism.PrimordialTension.mark_step_iff_unmark (Nothing := NObj) anchor).2 hUnmark)

def mul (x y : AnchoredPreGame) : AnchoredPreGame :=
  { core := SurrealCore.mul x.core y.core
    anchor := x.anchor
    polarity := x.polarity
    anchor_valid := x.anchor_valid }

end AnchoredPreGame

abbrev anchoredAdd : AnchoredPreGame → AnchoredPreGame → AnchoredPreGame :=
  AnchoredPreGame.add

abbrev anchoredNeg : AnchoredPreGame → AnchoredPreGame :=
  AnchoredPreGame.neg

abbrev anchoredMul : AnchoredPreGame → AnchoredPreGame → AnchoredPreGame :=
  AnchoredPreGame.mul

@[simp] theorem forget_add (x y : AnchoredPreGame) :
    forget (anchoredAdd x y) = SurrealCore.add x.core y.core := rfl

@[simp] theorem forget_mul (x y : AnchoredPreGame) :
    forget (anchoredMul x y) = SurrealCore.mul x.core y.core := rfl

@[simp] theorem forget_neg (x : AnchoredPreGame) :
    forget (anchoredNeg x) = SurrealCore.neg x.core := by
  cases x with
  | mk core anchor polarity anchor_valid =>
      cases polarity <;> rfl

@[simp] theorem add_anchor (x y : AnchoredPreGame) :
    (anchoredAdd x y).anchor = x.anchor := rfl

@[simp] theorem add_polarity (x y : AnchoredPreGame) :
    (anchoredAdd x y).polarity = x.polarity := rfl

@[simp] theorem mul_anchor (x y : AnchoredPreGame) :
    (anchoredMul x y).anchor = x.anchor := rfl

@[simp] theorem mul_polarity (x y : AnchoredPreGame) :
    (anchoredMul x y).polarity = x.polarity := rfl

@[simp] theorem neg_anchor_step (x : AnchoredPreGame) :
    (anchoredNeg x).anchor = stepN x.anchor := by
  cases x with
  | mk core anchor polarity anchor_valid =>
      cases polarity <;> rfl

@[simp] theorem neg_marked_polarity
    (core : PreGame) (anchor : NObj) (hMark : IsMark anchor) :
    (anchoredNeg ⟨core, anchor, .mark, hMark⟩).polarity = .unmark := rfl

@[simp] theorem neg_unmarked_polarity
    (core : PreGame) (anchor : NObj) (hUnmark : IsUnmark anchor) :
    (anchoredNeg ⟨core, anchor, .unmark, hUnmark⟩).polarity = .mark := rfl

end

end Surreal
end Numbers
end HeytingLean
