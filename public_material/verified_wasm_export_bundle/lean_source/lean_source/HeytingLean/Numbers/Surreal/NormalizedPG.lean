import HeytingLean.Numbers.SurrealCore

namespace HeytingLean
namespace Numbers
namespace Surreal

/-!
  Normalized PreGames: a closure via `canonicalize` on the minimal
  `PreGame` skeleton. This is a lightweight layer that avoids the
  heavier rank-indexed `Game` machinery, so it compiles strictly
  without further dependencies.
-/

/-- A pre-game is in normal form when `canonicalize g = g`. -/
def IsCanon (g : HeytingLean.Numbers.SurrealCore.PreGame) : Prop :=
  HeytingLean.Numbers.SurrealCore.canonicalize g = g

/-- Subtype of canonicalized pre-games. -/
def Canon := { g : HeytingLean.Numbers.SurrealCore.PreGame // IsCanon g }

namespace Canon

/-- Project any pre-game to its canonical representative. -/
def of (g : HeytingLean.Numbers.SurrealCore.PreGame) : Canon :=
  ⟨HeytingLean.Numbers.SurrealCore.canonicalize g, by
    simp [IsCanon, HeytingLean.Numbers.SurrealCore.canonicalize_idem]⟩

/-- Underlying pre-game. -/
def val (x : Canon) : HeytingLean.Numbers.SurrealCore.PreGame := x.1

instance : Coe Canon HeytingLean.Numbers.SurrealCore.PreGame where
  coe := val

theorem val_of (g : HeytingLean.Numbers.SurrealCore.PreGame) :
    (of g).1 = HeytingLean.Numbers.SurrealCore.canonicalize g := rfl

theorem isCanon_val (x : Canon) : IsCanon x.1 := x.2

end Canon

end Surreal
end Numbers
end HeytingLean
