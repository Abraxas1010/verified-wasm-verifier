import HeytingLean.Genesis.CoGame
import Mathlib.Logic.Relation

/-!
# Genesis.KnotSetGraph

Minimal self-membership graph layer for virtual/knot-style paradox semantics.
-/

namespace HeytingLean.Genesis

universe u v

/-- A minimal membership graph. -/
structure MemGraph where
  Node : Type u
  mem : Node → Node → Prop

namespace MemGraph

variable (G : MemGraph)

/-- Back-and-forth condition for a relation on graph nodes. -/
def IsBisimulation (R : G.Node → G.Node → Prop) : Prop :=
  ∀ ⦃x y : G.Node⦄, R x y →
    (∀ a : G.Node, G.mem a x → ∃ b : G.Node, G.mem b y ∧ R a b) ∧
    (∀ b : G.Node, G.mem b y → ∃ a : G.Node, G.mem a x ∧ R a b)

/-- Bisimilarity as existence of a bisimulation relation containing `(x,y)`. -/
def Bisim : G.Node → G.Node → Prop :=
  fun x y => ∃ R : G.Node → G.Node → Prop, IsBisimulation G R ∧ R x y

theorem isBisimulation_eq : IsBisimulation G (fun x y => x = y) := by
  intro x y hxy
  subst hxy
  refine ⟨?_, ?_⟩
  · intro a ha
    exact ⟨a, ha, rfl⟩
  · intro b hb
    exact ⟨b, hb, rfl⟩

theorem bisim_refl : Reflexive (Bisim G) := by
  intro x
  exact ⟨(fun a b => a = b), isBisimulation_eq (G := G), rfl⟩

theorem isBisimulation_converse {R : G.Node → G.Node → Prop}
    (hR : IsBisimulation G R) :
    IsBisimulation G (fun x y => R y x) := by
  intro x y hxy
  have h := hR (x := y) (y := x) hxy
  refine ⟨?_, ?_⟩
  · intro a ha
    rcases h.2 a ha with ⟨b, hb, hba⟩
    exact ⟨b, hb, hba⟩
  · intro b hb
    rcases h.1 b hb with ⟨a, ha, hba⟩
    exact ⟨a, ha, hba⟩

theorem bisim_symm : Symmetric (Bisim G) := by
  intro x y hxy
  rcases hxy with ⟨R, hR, hRxy⟩
  exact ⟨(fun a b => R b a), isBisimulation_converse (G := G) hR, hRxy⟩

theorem isBisimulation_comp {R S : G.Node → G.Node → Prop}
    (hR : IsBisimulation G R) (hS : IsBisimulation G S) :
    IsBisimulation G (fun x z => ∃ y, R x y ∧ S y z) := by
  intro x z hxz
  rcases hxz with ⟨y, hxy, hyz⟩
  have hxy' := hR (x := x) (y := y) hxy
  have hyz' := hS (x := y) (y := z) hyz
  refine ⟨?_, ?_⟩
  · intro a ha
    rcases hxy'.1 a ha with ⟨b, hb, hab⟩
    rcases hyz'.1 b hb with ⟨c, hc, hbc⟩
    exact ⟨c, hc, ⟨b, hab, hbc⟩⟩
  · intro c hc
    rcases hyz'.2 c hc with ⟨b, hb, hbc⟩
    rcases hxy'.2 b hb with ⟨a, ha, hab⟩
    exact ⟨a, ha, ⟨b, hab, hbc⟩⟩

theorem bisim_trans : Transitive (Bisim G) := by
  intro x y z hxy hyz
  rcases hxy with ⟨R, hR, hRxy⟩
  rcases hyz with ⟨S, hS, hSyz⟩
  let RS : G.Node → G.Node → Prop := fun a c => ∃ b, R a b ∧ S b c
  refine ⟨RS, ?_, ?_⟩
  · exact isBisimulation_comp (G := G) hR hS
  · exact ⟨y, hRxy, hSyz⟩

theorem bisim_equiv : Equivalence (Bisim G) where
  refl := bisim_refl (G := G)
  symm := by
    intro x y hxy
    exact bisim_symm (G := G) hxy
  trans := by
    intro x y z hxy hyz
    exact bisim_trans (G := G) hxy hyz

/-- Forgetful translator from membership graphs into symmetric left/right co-games. -/
def toCoGame (G : MemGraph) (root : G.Node) : CoGame where
  Node := G.Node
  root := root
  leftSucc x := {y | G.mem y x}
  rightSucc x := {y | G.mem y x}

end MemGraph

/-- `Ω = {Ω}` encoded as one node with self-membership. -/
def OmegaGraph : MemGraph where
  Node := Unit
  mem _ _ := True

def Omega : OmegaGraph.Node := ()

theorem omega_mem_self : OmegaGraph.mem Omega Omega := by
  trivial

/-- Two-node mutual-membership graph (`A={B}, B={A}`). -/
def LinkGraph : MemGraph where
  Node := Bool
  mem a b := a ≠ b

def LinkA : LinkGraph.Node := true
def LinkB : LinkGraph.Node := false

theorem link_mutual : LinkGraph.mem LinkA LinkB ∧ LinkGraph.mem LinkB LinkA := by
  simp [LinkGraph, LinkA, LinkB]

theorem omega_toCoGame_bisim_life :
    CoGame.Bisim (MemGraph.toCoGame OmegaGraph Omega) CoGame.Life := by
  refine ⟨fun _ _ => True, ?_⟩
  refine CoGame.IsBisim.mk ?_ ?_ ?_ ?_ ?_
  · trivial
  · intro x y hxy x' hx'
    cases x
    cases y
    cases x'
    refine ⟨(), ?_, trivial⟩
    change () = ()
    rfl
  · intro x y hxy y' hy'
    cases x
    cases y
    cases y'
    refine ⟨(), ?_, trivial⟩
    change True
    trivial
  · intro x y hxy x' hx'
    cases x
    cases y
    cases x'
    refine ⟨(), ?_, trivial⟩
    change () = ()
    rfl
  · intro x y hxy y' hy'
    cases x
    cases y
    cases y'
    refine ⟨(), ?_, trivial⟩
    change True
    trivial

end HeytingLean.Genesis
