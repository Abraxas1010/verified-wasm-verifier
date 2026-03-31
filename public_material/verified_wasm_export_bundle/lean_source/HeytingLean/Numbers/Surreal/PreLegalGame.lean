import HeytingLean.Numbers.Surreal.NoneistFoundation

/-!
# Surreal.PreLegalGame

SN-014 baseline: pre-legal games (cuts without Conway legality), with bridges to
legal fragments when cut conditions are supplied.
-/

namespace HeytingLean
namespace Numbers
namespace Surreal

open HeytingLean.Numbers.SurrealCore

/-- Pre-legal cut object (no legality side-condition baked into the type). -/
structure PreLegalGame where
  L : List PreGame := []
  R : List PreGame := []
  deriving Repr

namespace PreLegalGame

/-- Reinterpret a pre-legal cut as a pre-game via the standard birth constructor. -/
def toPreGame (g : PreLegalGame) : PreGame :=
  PreGame.build g.L g.R

/-- Explicit cut legality predicate for pre-legal cuts. -/
noncomputable def legalCut (g : PreLegalGame) : Prop :=
  ∀ l ∈ g.L, ∀ r ∈ g.R, SurrealCore.lt l r

/-- Contradictory cut: at least one violating left/right witness pair. -/
noncomputable def contradictory (g : PreLegalGame) : Prop :=
  ∃ l ∈ g.L, ∃ r ∈ g.R, ¬ SurrealCore.lt l r

/-- Cross-leg legality between two pre-legal cuts (needed for legal sum). -/
noncomputable def crossLegal (x y : PreLegalGame) : Prop :=
  (∀ l ∈ x.L, ∀ r ∈ y.R, SurrealCore.lt l r) ∧
    (∀ l ∈ y.L, ∀ r ∈ x.R, SurrealCore.lt l r)

theorem not_contradictory_of_legalCut (g : PreLegalGame) (h : legalCut g) :
    ¬ contradictory g := by
  intro hc
  rcases hc with ⟨l, hl, r, hr, hbad⟩
  exact hbad (h l hl r hr)

theorem legal_of_legalCut (g : PreLegalGame) (h : legalCut g) :
    SurrealCore.legal (toPreGame g) := by
  intro l hl r hr
  exact h l hl r hr

/-- Appending two legal cuts remains legal when cross-leg constraints hold. -/
theorem legalCut_append
    (x y : PreLegalGame)
    (hx : legalCut x) (hy : legalCut y) (hxy : crossLegal x y) :
    legalCut { L := x.L ++ y.L, R := x.R ++ y.R } := by
  intro l hl r hr
  rcases List.mem_append.1 hl with hlx | hly
  · rcases List.mem_append.1 hr with hrx | hry
    · exact hx l hlx r hrx
    · exact hxy.1 l hlx r hry
  · rcases List.mem_append.1 hr with hrx | hry
    · exact hxy.2 l hly r hrx
    · exact hy l hly r hry

/-- Contradictions are preserved when extending by append on the right. -/
theorem contradictory_append_left (x y : PreLegalGame) (hx : contradictory x) :
    contradictory { L := x.L ++ y.L, R := x.R ++ y.R } := by
  rcases hx with ⟨l, hl, r, hr, hbad⟩
  refine ⟨l, ?_, r, ?_, hbad⟩
  · exact List.mem_append.2 (Or.inl hl)
  · exact List.mem_append.2 (Or.inl hr)

/-- Contradictions are preserved when extending by append on the left. -/
theorem contradictory_append_right (x y : PreLegalGame) (hy : contradictory y) :
    contradictory { L := x.L ++ y.L, R := x.R ++ y.R } := by
  rcases hy with ⟨l, hl, r, hr, hbad⟩
  refine ⟨l, ?_, r, ?_, hbad⟩
  · exact List.mem_append.2 (Or.inr hl)
  · exact List.mem_append.2 (Or.inr hr)

/-- Forget an anchored noneist game into a pre-legal cut. -/
def ofAnchored (g : AnchoredPreGame) : PreLegalGame :=
  { L := g.core.L, R := g.core.R }

@[simp] theorem ofAnchored_toPreGame (g : AnchoredPreGame) :
    (ofAnchored g).toPreGame = PreGame.build g.core.L g.core.R := rfl

/-- Empty cut is trivially legal in the pre-legal layer. -/
@[simp] theorem legalCut_empty : legalCut ({ L := [], R := [] } : PreLegalGame) := by
  intro l hl
  simp at hl

@[simp] theorem not_contradictory_empty :
    ¬ contradictory ({ L := [], R := [] } : PreLegalGame) := by
  exact not_contradictory_of_legalCut _ legalCut_empty

@[simp] theorem crossLegal_empty_left (x : PreLegalGame) :
    crossLegal ({ L := [], R := [] } : PreLegalGame) x := by
  constructor
  · intro l hl
    simp at hl
  · intro l hl r hr
    simp at hr

@[simp] theorem crossLegal_empty_right (x : PreLegalGame) :
    crossLegal x ({ L := [], R := [] } : PreLegalGame) := by
  constructor
  · intro l hl r hr
    simp at hr
  · intro l hl
    simp at hl

end PreLegalGame

end Surreal
end Numbers
end HeytingLean
