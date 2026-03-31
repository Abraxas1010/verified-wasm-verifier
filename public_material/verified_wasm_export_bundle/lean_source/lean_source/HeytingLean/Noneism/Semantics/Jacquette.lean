import HeytingLean.Noneism.Semantics.LP

namespace HeytingLean
namespace Noneism
namespace Jacquette

/- Intensional identity via LP-designated predication. -/

structure Property (D : Type) where
  eval : D → LP.TV

def designated {D} (F : Property D) (x : D) : Prop := LP.TV.designated (F.eval x)

/-- Intensional identity: a and b agree on all LP-designated properties. -/
def ident {D} (a b : D) : Prop := ∀ F : Property D, designated F a ↔ designated F b

theorem ident_refl {D} (a : D) : ident a a := by
  intro F; simp [designated]

theorem ident_symm {D} {a b : D} : ident a b → ident b a := by
  intro h F; simpa [ident] using (h F).symm

theorem ident_trans {D} {a b c : D} : ident a b → ident b c → ident a c := by
  intro h1 h2 F
  exact Iff.trans (h1 F) (h2 F)

-- Additional LP-valued examples live under `Noneism/Tests/Jacquette.lean`.

end Jacquette
end Noneism
end HeytingLean
