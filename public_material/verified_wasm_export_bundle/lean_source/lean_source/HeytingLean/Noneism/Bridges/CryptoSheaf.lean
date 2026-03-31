import HeytingLean.Noneism.Semantics.Sylvan
import HeytingLean.LoF.CryptoSheaf.Site
import HeytingLean.LoF.CryptoSheaf.ZKMorphism
import HeytingLean.LoF.CryptoSheaf.Presheaf

/-
Noneism ↔ CryptoSheaf Bridge (baseline)

Provides a minimal local site and example ZK morphism wired to the Noneism layer.
This stays lightweight and does not claim semantic adequacy; it is a compile-time
bridge and a template for richer connections.
-/

namespace HeytingLean
namespace Noneism
namespace Bridge
namespace CryptoSheaf

open HeytingLean.LoF

/-- A trivial one-object site over `Unit` with `Prop` logic. -/
def unitSite : LoF.CryptoSheaf.PosetSite Unit where
  Logic := fun _ => Prop
  heytingInst := fun _ => inferInstance
  restrict := by intro U V h; exact id
  restrictHom := by intro U V h; exact HeytingHom.id _
  restrictHom_toFun := by intro U V h; rfl
  restrict_id := by intro U x; cases U; rfl
  restrict_comp := by intro U V W hVU hWV x; cases U; cases V; cases W; rfl

/-- A degenerate ZK morphism over `unitSite` that always proves `True`. -/
def trivialZK : LoF.CryptoSheaf.ZKMorphism unitSite () () where
  Witness := Unit
  statement := True
  prove := fun _ _ => True
  sound := by intro _ _; trivial
  simulator := fun _ => True
  zk_simulates := by intro _; exact ⟨(), rfl⟩

end CryptoSheaf
end Bridge
end Noneism
end HeytingLean
