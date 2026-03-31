import HeytingLean.LoF.CryptoSheaf.Site
import HeytingLean.LoF.CryptoSheaf.ZKMorphism

/-
CryptoSheaf/Examples/ZKModCompose

Minimal example showing `ZKModMorphism.compose` typechecks on a trivial site
where logic is `Prop` and the statement is `True`.
-/

namespace HeytingLean
namespace LoF
namespace CryptoSheaf
namespace Examples

def unitSite : PosetSite Unit where
  Logic := fun _ => Prop
  heytingInst := fun _ => inferInstance
  restrict := by intro U V h; exact id
  restrictHom := by intro U V h; exact HeytingHom.id _
  restrictHom_toFun := by intro U V h; rfl
  restrict_id := by intro U x; cases U; rfl
  restrict_comp := by intro U V W hVU hWV x; cases U; cases V; cases W; rfl

def trivialZKMod : ZKModMorphism unitSite () () where
  toZKMorphism :=
    { Witness := Unit
      statement := True
      prove := fun _ _ => True
      sound := by intro _ _; trivial
      simulator := fun _ => True
      zk_simulates := by intro _; exact ⟨(), rfl⟩ }
  zk_mod := by
    intro input
    refine ⟨(), ?_⟩
    -- In `Prop`, `x ⇨ True` is definitionally `True`, so equality is trivial.
    rfl

example : (ZKModMorphism.compose (S := unitSite) (U := ()) (V := ()) (W := ()) trivialZKMod trivialZKMod).toZKMorphism.statement = True := rfl

end Examples
end CryptoSheaf
end LoF
end HeytingLean

