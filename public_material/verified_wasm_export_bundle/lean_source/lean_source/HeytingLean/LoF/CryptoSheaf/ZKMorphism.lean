import HeytingLean.LoF.CryptoSheaf.Site

/-
CryptoSheaf/ZKMorphism

Zero-knowledge morphisms between contexts of a `PosetSite`. The ZK property is
captured as existence of a simulator producing outputs equal to real proofs.
-/

namespace HeytingLean
namespace LoF
namespace CryptoSheaf

variable {C : Type _} [PartialOrder C]

structure ZKMorphism (S : PosetSite C) (U V : C) where
  Witness : Type
  statement : S.Logic V
  prove : Witness → S.Logic U → S.Logic V
  sound : ∀ (w : Witness) (input : S.Logic U), prove w input ≤ statement
  simulator : S.Logic U → S.Logic V
  zk_simulates : ∀ (input : S.Logic U), ∃ (w : Witness), simulator input = prove w input

namespace ZKMorphism

variable {S : PosetSite C} {U V W : C}

def compose (f : ZKMorphism S U V) (g : ZKMorphism S V W) : ZKMorphism S U W where
  Witness := f.Witness × g.Witness
  statement := g.statement
  prove := fun ⟨wf, wg⟩ input => g.prove wg (f.prove wf input)
  sound := by
    intro ⟨wf, wg⟩ input
    exact le_trans (g.sound wg (f.prove wf input)) (le_of_eq rfl)
  simulator := fun input => g.simulator (f.simulator input)
  zk_simulates := by
    intro input
    obtain ⟨wf, h1⟩ := f.zk_simulates input
    obtain ⟨wg, h2⟩ := g.zk_simulates (f.simulator input)
    refine ⟨⟨wf, wg⟩, ?_⟩
    -- Rewrite both sides using h1 on the inner argument.
    simpa [h1] using h2

end ZKMorphism

/- Indistinguishability modulo the statement via Heyting implication. -/
def indistMod {S : PosetSite C} {V : C} (stmt : S.Logic V)
    (x y : S.Logic V) : Prop := (x ⇨ stmt) = (y ⇨ stmt)

structure ZKModMorphism (S : PosetSite C) (U V : C)
    extends ZKMorphism S U V where
  zk_mod : ∀ (input : S.Logic U), ∃ (w : Witness),
    indistMod (S := S) (V := V) statement (simulator input) (prove w input)

namespace ZKModMorphism

variable {S : PosetSite C} {U V W : C}

def compose (f : ZKModMorphism S U V) (g : ZKModMorphism S V W) :
    ZKModMorphism S U W where
  toZKMorphism := ZKMorphism.compose f.toZKMorphism g.toZKMorphism
  zk_mod := by
    intro input
    obtain ⟨wf, hEq⟩ := f.zk_simulates input
    obtain ⟨wg, hg⟩ := g.zk_mod (f.simulator input)
    -- Unfold the indistinguishability equality.
    have hg' : g.simulator (f.simulator input) ⇨ g.statement
              = g.prove wg (f.simulator input) ⇨ g.statement := by
      simpa [indistMod] using hg
    refine ⟨⟨wf, wg⟩, ?_⟩
    -- Directly rewrite the composed goal using `hg'` and `hEq`.
    simpa [indistMod, ZKMorphism.compose, hEq] using hg'

end ZKModMorphism

/-! ### Indistinguishability is an equivalence relation (modulo the statement) -/

section IndistEq

variable {S : PosetSite C} {V : C}

theorem indistMod_refl (stmt x : S.Logic V) : indistMod (S := S) (V := V) stmt x x := rfl

theorem indistMod_symm (stmt : S.Logic V) {x y : S.Logic V}
    (h : indistMod (S := S) (V := V) stmt x y) : indistMod stmt y x := by
  simpa [indistMod] using h.symm

theorem indistMod_trans (stmt : S.Logic V) {x y z : S.Logic V}
    (hxy : indistMod (S := S) (V := V) stmt x y)
    (hyz : indistMod (S := S) (V := V) stmt y z) : indistMod stmt x z := by
  simpa [indistMod] using hxy.trans hyz

end IndistEq

structure ZKProofSystem (S : PosetSite C) where
  morphisms : ∀ {U V : C}, List (ZKMorphism S U V)
  has_id : ∀ U : C, ∃ m ∈ morphisms (U := U) (V := U), m.statement = ⊤
  compose_closed : ∀ {U V W : C} (f : ZKMorphism S U V) (g : ZKMorphism S V W),
    f ∈ morphisms → g ∈ morphisms → ZKMorphism.compose f g ∈ morphisms

end CryptoSheaf
end LoF
end HeytingLean
