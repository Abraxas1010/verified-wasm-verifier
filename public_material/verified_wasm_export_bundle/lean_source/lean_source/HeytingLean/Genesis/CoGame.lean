import Mathlib.SetTheory.PGame.Basic

set_option linter.deprecated.module false

/-!
# Genesis.CoGame

Graph-based coinductive games for Genesis Phase 1.

The core representation is a rooted directed graph with Left/Right-labeled
successor relations. Cycles are allowed by construction.
-/

namespace HeytingLean.Genesis

universe u v w

/-- A coinductive game as a rooted directed graph with left/right successor sets. -/
structure CoGame where
  Node : Type u
  root : Node
  leftSucc : Node → Set Node
  rightSucc : Node → Set Node

namespace CoGame

/-- The canonical empty-option game (single node, no outgoing edges). -/
def Void : CoGame where
  Node := Unit
  root := ()
  leftSucc _ := ∅
  rightSucc _ := ∅

/-- `Life = {Life | Life}` as a one-node self-loop graph. -/
def Life : CoGame where
  Node := Unit
  root := ()
  leftSucc _ := {()}
  rightSucc _ := {()}

@[simp] theorem void_left_empty (n : Void.Node) : n ∉ Void.leftSucc Void.root := by
  intro h
  simpa [Void] using h

@[simp] theorem void_right_empty (n : Void.Node) : n ∉ Void.rightSucc Void.root := by
  intro h
  simpa [Void] using h

@[simp] theorem life_left_root_mem : Life.root ∈ Life.leftSucc Life.root := by
  change () = ()
  rfl

@[simp] theorem life_right_root_mem : Life.root ∈ Life.rightSucc Life.root := by
  change () = ()
  rfl

/-- Bisimulation predicate between two graph co-games. -/
structure IsBisim (G : CoGame.{u}) (H : CoGame.{v}) (R : G.Node → H.Node → Prop) : Prop where
  root_rel : R G.root H.root
  left_forth :
    ∀ {x y}, R x y → ∀ {x'}, x' ∈ G.leftSucc x → ∃ y', y' ∈ H.leftSucc y ∧ R x' y'
  left_back :
    ∀ {x y}, R x y → ∀ {y'}, y' ∈ H.leftSucc y → ∃ x', x' ∈ G.leftSucc x ∧ R x' y'
  right_forth :
    ∀ {x y}, R x y → ∀ {x'}, x' ∈ G.rightSucc x → ∃ y', y' ∈ H.rightSucc y ∧ R x' y'
  right_back :
    ∀ {x y}, R x y → ∀ {y'}, y' ∈ H.rightSucc y → ∃ x', x' ∈ G.rightSucc x ∧ R x' y'

/-- Root bisimilarity between co-games. -/
def Bisim (G : CoGame.{u}) (H : CoGame.{v}) : Prop :=
  ∃ R : G.Node → H.Node → Prop, IsBisim G H R

theorem bisim_refl (G : CoGame.{u}) : Bisim G G := by
  refine ⟨fun x y => x = y, ?_⟩
  refine IsBisim.mk ?_ ?_ ?_ ?_ ?_
  · rfl
  · intro x y hxy x' hx'
    subst hxy
    exact ⟨x', hx', rfl⟩
  · intro x y hxy y' hy'
    subst hxy
    exact ⟨y', hy', rfl⟩
  · intro x y hxy x' hx'
    subst hxy
    exact ⟨x', hx', rfl⟩
  · intro x y hxy y' hy'
    subst hxy
    exact ⟨y', hy', rfl⟩

theorem bisim_symm {G : CoGame.{u}} {H : CoGame.{v}} : Bisim G H → Bisim H G := by
  intro h
  rcases h with ⟨R, hR⟩
  refine ⟨fun y x => R x y, ?_⟩
  refine IsBisim.mk ?_ ?_ ?_ ?_ ?_
  · exact hR.root_rel
  · intro x y hxy x' hx'
    rcases hR.left_back hxy hx' with ⟨y', hy', hrel⟩
    exact ⟨y', hy', hrel⟩
  · intro x y hxy y' hy'
    rcases hR.left_forth hxy hy' with ⟨x', hx', hrel⟩
    exact ⟨x', hx', hrel⟩
  · intro x y hxy x' hx'
    rcases hR.right_back hxy hx' with ⟨y', hy', hrel⟩
    exact ⟨y', hy', hrel⟩
  · intro x y hxy y' hy'
    rcases hR.right_forth hxy hy' with ⟨x', hx', hrel⟩
    exact ⟨x', hx', hrel⟩

theorem bisim_trans {G : CoGame.{u}} {H : CoGame.{v}} {K : CoGame.{w}} :
    Bisim G H → Bisim H K → Bisim G K := by
  intro hGH hHK
  rcases hGH with ⟨R, hR⟩
  rcases hHK with ⟨S, hS⟩
  let T : G.Node → K.Node → Prop := fun x z => ∃ y, R x y ∧ S y z
  refine ⟨T, ?_⟩
  refine IsBisim.mk ?_ ?_ ?_ ?_ ?_
  · exact ⟨H.root, hR.root_rel, hS.root_rel⟩
  · intro x z hxz x' hx'
    rcases hxz with ⟨y, hxy, hyz⟩
    rcases hR.left_forth hxy hx' with ⟨y', hy'mem, hx'y'⟩
    rcases hS.left_forth hyz hy'mem with ⟨z', hz'mem, hy'z'⟩
    exact ⟨z', hz'mem, ⟨y', hx'y', hy'z'⟩⟩
  · intro x z hxz z' hz'
    rcases hxz with ⟨y, hxy, hyz⟩
    rcases hS.left_back hyz hz' with ⟨y', hy'mem, hy'z'⟩
    rcases hR.left_back hxy hy'mem with ⟨x', hx'mem, hx'y'⟩
    exact ⟨x', hx'mem, ⟨y', hx'y', hy'z'⟩⟩
  · intro x z hxz x' hx'
    rcases hxz with ⟨y, hxy, hyz⟩
    rcases hR.right_forth hxy hx' with ⟨y', hy'mem, hx'y'⟩
    rcases hS.right_forth hyz hy'mem with ⟨z', hz'mem, hy'z'⟩
    exact ⟨z', hz'mem, ⟨y', hx'y', hy'z'⟩⟩
  · intro x z hxz z' hz'
    rcases hxz with ⟨y, hxy, hyz⟩
    rcases hS.right_back hyz hz' with ⟨y', hy'mem, hy'z'⟩
    rcases hR.right_back hxy hy'mem with ⟨x', hx'mem, hx'y'⟩
    exact ⟨x', hx'mem, ⟨y', hx'y', hy'z'⟩⟩

instance : Setoid CoGame where
  r := Bisim
  iseqv := ⟨bisim_refl, bisim_symm, bisim_trans⟩

open SetTheory

/-- Embed a well-founded `PGame` into graph-based `CoGame`. -/
def ofPGame (g : SetTheory.PGame) : CoGame where
  Node := SetTheory.PGame
  root := g
  leftSucc x := {x' | ∃ i : x.LeftMoves, x' = x.moveLeft i}
  rightSucc x := {x' | ∃ j : x.RightMoves, x' = x.moveRight j}

@[simp] theorem mem_leftSucc_ofPGame {g x x' : SetTheory.PGame} :
    x' ∈ (ofPGame g).leftSucc x ↔ ∃ i : x.LeftMoves, x' = x.moveLeft i := Iff.rfl

@[simp] theorem mem_rightSucc_ofPGame {g x x' : SetTheory.PGame} :
    x' ∈ (ofPGame g).rightSucc x ↔ ∃ j : x.RightMoves, x' = x.moveRight j := Iff.rfl

/-- Relabellings of `PGame` induce bisimilar `CoGame` embeddings. -/
theorem ofPGame_bisim_of_relabelling {x y : SetTheory.PGame}
    (hxy : SetTheory.PGame.Relabelling x y) : Bisim (ofPGame x) (ofPGame y) := by
  refine ⟨fun a b => Nonempty (SetTheory.PGame.Relabelling a b), ?_⟩
  refine IsBisim.mk ?_ ?_ ?_ ?_ ?_
  · exact ⟨hxy⟩
  · intro a b hab a' ha'
    rcases hab with ⟨r⟩
    rcases ha' with ⟨i, rfl⟩
    let j : b.LeftMoves := r.leftMovesEquiv i
    refine ⟨b.moveLeft j, ?_, ?_⟩
    · exact ⟨j, rfl⟩
    · exact ⟨r.moveLeft i⟩
  · intro a b hab b' hb'
    rcases hab with ⟨r⟩
    rcases hb' with ⟨j, rfl⟩
    let i : a.LeftMoves := r.leftMovesEquiv.symm j
    refine ⟨a.moveLeft i, ?_, ?_⟩
    · exact ⟨i, rfl⟩
    · exact ⟨r.moveLeftSymm j⟩
  · intro a b hab a' ha'
    rcases hab with ⟨r⟩
    rcases ha' with ⟨i, rfl⟩
    let j : b.RightMoves := r.rightMovesEquiv i
    refine ⟨b.moveRight j, ?_, ?_⟩
    · exact ⟨j, rfl⟩
    · exact ⟨r.moveRight i⟩
  · intro a b hab b' hb'
    rcases hab with ⟨r⟩
    rcases hb' with ⟨j, rfl⟩
    let i : a.RightMoves := r.rightMovesEquiv.symm j
    refine ⟨a.moveRight i, ?_, ?_⟩
    · exact ⟨i, rfl⟩
    · exact ⟨r.moveRightSymm j⟩

theorem ofPGame_bisim_self (x : SetTheory.PGame) : Bisim (ofPGame x) (ofPGame x) :=
  ofPGame_bisim_of_relabelling (x := x) (y := x) (SetTheory.PGame.Relabelling.refl x)

theorem life_bisim_self : Bisim Life Life := bisim_refl Life
theorem void_bisim_self : Bisim Void Void := bisim_refl Void

end CoGame
end HeytingLean.Genesis
