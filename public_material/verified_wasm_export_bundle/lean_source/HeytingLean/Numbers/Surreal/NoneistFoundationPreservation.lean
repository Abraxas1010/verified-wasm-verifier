import HeytingLean.Numbers.Surreal.NoneistFoundation
import HeytingLean.Numbers.Surreal.BridgeToPGamePreservation

namespace HeytingLean
namespace Numbers
namespace Surreal

open HeytingLean.Numbers.SurrealCore

/-- Forgetful semantics: anchored addition preserves `toIGame` addition. -/
theorem forget_toIGame_add (x y : AnchoredPreGame) :
    SurrealCore.PreGame.toIGame (forget (anchoredAdd x y)) =
      SurrealCore.PreGame.toIGame (forget x) + SurrealCore.PreGame.toIGame (forget y) := by
  simpa [forget_add] using SurrealCore.PreGame.toIGame_add x.core y.core

/-- Forgetful semantics: anchored negation preserves `toIGame` negation. -/
theorem forget_toIGame_neg (x : AnchoredPreGame) :
    SurrealCore.PreGame.toIGame (forget (anchoredNeg x)) =
      -SurrealCore.PreGame.toIGame (forget x) := by
  simpa [forget_neg] using SurrealCore.PreGame.toIGame_neg x.core

/-- Forgetful semantics: anchored multiplication preserves `toIGame` multiplication. -/
theorem forget_toIGame_mul (x y : AnchoredPreGame) :
    SurrealCore.PreGame.toIGame (forget (anchoredMul x y)) =
      SurrealCore.PreGame.toIGame (forget x) * SurrealCore.PreGame.toIGame (forget y) := by
  simpa [forget_mul] using SurrealCore.PreGame.toIGame_mul x.core y.core

/-- Anchored addition is semantically commutative through the forgetful bridge. -/
theorem forget_toIGame_add_comm (x y : AnchoredPreGame) :
    SurrealCore.PreGame.toIGame (forget (anchoredAdd x y)) =
      SurrealCore.PreGame.toIGame (forget (anchoredAdd y x)) := by
  simpa [forget_add] using SurrealCore.PreGame.toIGame_add_comm x.core y.core

/-- Anchored addition is semantically associative through the forgetful bridge. -/
theorem forget_toIGame_add_assoc (x y z : AnchoredPreGame) :
    SurrealCore.PreGame.toIGame (forget (anchoredAdd (anchoredAdd x y) z)) =
      SurrealCore.PreGame.toIGame (forget (anchoredAdd x (anchoredAdd y z))) := by
  simpa [forget_add] using SurrealCore.PreGame.toIGame_add_assoc x.core y.core z.core

/-- Anchored negation provides an additive inverse up to game equivalence. -/
theorem forget_toIGame_add_left_neg_equiv_zero (x : AnchoredPreGame) :
    SurrealCore.PreGame.toIGame (forget (anchoredAdd (anchoredNeg x) x)) ≈ 0 := by
  have hcore : (anchoredNeg x).core = SurrealCore.neg x.core := by
    simpa [forget] using (forget_neg x)
  simpa [forget_add, hcore] using
    SurrealCore.PreGame.toIGame_add_left_neg_equiv_zero x.core

/-- Symmetric additive inverse form for anchored games (up to equivalence). -/
theorem forget_toIGame_add_right_neg_equiv_zero (x : AnchoredPreGame) :
    SurrealCore.PreGame.toIGame (forget (anchoredAdd x (anchoredNeg x))) ≈ 0 := by
  have hcore : (anchoredNeg x).core = SurrealCore.neg x.core := by
    simpa [forget] using (forget_neg x)
  simpa [forget_add, hcore] using
    SurrealCore.PreGame.toIGame_add_right_neg_equiv_zero x.core

/-- Anchored left additive cancellation (up to game equivalence) through forgetful semantics. -/
theorem forget_toIGame_add_left_cancel_equiv (x y : AnchoredPreGame) :
    SurrealCore.PreGame.toIGame (forget (anchoredAdd (anchoredNeg x) (anchoredAdd x y))) ≈
      SurrealCore.PreGame.toIGame (forget y) := by
  have hneg : (anchoredNeg x).core = SurrealCore.neg x.core := by
    simpa [forget] using (forget_neg x)
  have haddxy : (anchoredAdd x y).core = SurrealCore.add x.core y.core := by
    rfl
  simpa [forget_add, hneg, haddxy] using
    SurrealCore.PreGame.toIGame_add_left_cancel_equiv x.core y.core

/-- Anchored right additive cancellation (up to game equivalence) through forgetful semantics. -/
theorem forget_toIGame_add_right_cancel_equiv (x y : AnchoredPreGame) :
    SurrealCore.PreGame.toIGame (forget (anchoredAdd x (anchoredAdd (anchoredNeg x) y))) ≈
      SurrealCore.PreGame.toIGame (forget y) := by
  have hneg : (anchoredNeg x).core = SurrealCore.neg x.core := by
    simpa [forget] using (forget_neg x)
  have haddnegy : (anchoredAdd (anchoredNeg x) y).core =
      SurrealCore.add (SurrealCore.neg x.core) y.core := by
    calc
      (anchoredAdd (anchoredNeg x) y).core = SurrealCore.add (anchoredNeg x).core y.core := rfl
      _ = SurrealCore.add (SurrealCore.neg x.core) y.core := by simp [hneg]
  simpa [forget_add, hneg, haddnegy] using
    SurrealCore.PreGame.toIGame_add_right_cancel_equiv x.core y.core

/-- Anchored left distributivity of multiplication through the forgetful bridge
(up to game equivalence). -/
theorem forget_toIGame_mul_add_equiv (x y z : AnchoredPreGame) :
    SurrealCore.PreGame.toIGame (forget (anchoredMul x (anchoredAdd y z))) ≈
      SurrealCore.PreGame.toIGame
        (forget (anchoredAdd (anchoredMul x y) (anchoredMul x z))) := by
  simpa [forget_mul, forget_add] using
    SurrealCore.PreGame.toIGame_mul_add_equiv x.core y.core z.core

/-- Anchored right distributivity of multiplication through the forgetful bridge
(up to game equivalence). -/
theorem forget_toIGame_add_mul_equiv (x y z : AnchoredPreGame) :
    SurrealCore.PreGame.toIGame (forget (anchoredMul (anchoredAdd x y) z)) ≈
      SurrealCore.PreGame.toIGame
        (forget (anchoredAdd (anchoredMul x z) (anchoredMul y z))) := by
  simpa [forget_mul, forget_add] using
    SurrealCore.PreGame.toIGame_add_mul_equiv x.core y.core z.core

/-- Anchored associativity of multiplication through the forgetful bridge
(up to game equivalence). -/
theorem forget_toIGame_mul_assoc_equiv (x y z : AnchoredPreGame) :
    SurrealCore.PreGame.toIGame (forget (anchoredMul (anchoredMul x y) z)) ≈
      SurrealCore.PreGame.toIGame (forget (anchoredMul x (anchoredMul y z))) := by
  simpa [forget_mul] using
    SurrealCore.PreGame.toIGame_mul_assoc_equiv x.core y.core z.core

/-- Anchored commutativity of multiplication through the forgetful bridge. -/
theorem forget_toIGame_mul_comm (x y : AnchoredPreGame) :
    SurrealCore.PreGame.toIGame (forget (anchoredMul x y)) =
      SurrealCore.PreGame.toIGame (forget (anchoredMul y x)) := by
  simpa [forget_mul] using
    SurrealCore.PreGame.toIGame_mul_comm x.core y.core

/-- If an anchored game forgets to `nullCut`, it left-annihilates multiplication semantically. -/
theorem forget_toIGame_mul_nullCut_left
    (x y : AnchoredPreGame) (hx : forget x = SurrealCore.nullCut) :
    SurrealCore.PreGame.toIGame (forget (anchoredMul x y)) = 0 := by
  have hxcore : x.core = SurrealCore.nullCut := by
    simpa [forget] using hx
  calc
    SurrealCore.PreGame.toIGame (forget (anchoredMul x y))
        = SurrealCore.PreGame.toIGame (SurrealCore.mul x.core y.core) := by
            simp [forget_mul]
    _ = SurrealCore.PreGame.toIGame (SurrealCore.mul SurrealCore.nullCut y.core) := by
          rw [hxcore]
    _ = 0 := SurrealCore.PreGame.toIGame_mul_nullCut_left y.core

/-- If an anchored game forgets to `nullCut`, it right-annihilates multiplication semantically. -/
theorem forget_toIGame_mul_nullCut_right
    (x y : AnchoredPreGame) (hy : forget y = SurrealCore.nullCut) :
    SurrealCore.PreGame.toIGame (forget (anchoredMul x y)) = 0 := by
  have hycore : y.core = SurrealCore.nullCut := by
    simpa [forget] using hy
  calc
    SurrealCore.PreGame.toIGame (forget (anchoredMul x y))
        = SurrealCore.PreGame.toIGame (SurrealCore.mul x.core y.core) := by
            simp [forget_mul]
    _ = SurrealCore.PreGame.toIGame (SurrealCore.mul x.core SurrealCore.nullCut) := by
          rw [hycore]
    _ = 0 := SurrealCore.PreGame.toIGame_mul_nullCut_right x.core

/-- Anchored left distributive zero-fragment through forgetful semantics. -/
theorem forget_toIGame_mul_add_nullCut_left
    (x y z : AnchoredPreGame) (hx : forget x = SurrealCore.nullCut) :
    SurrealCore.PreGame.toIGame (forget (anchoredMul x (anchoredAdd y z))) =
      SurrealCore.PreGame.toIGame
        (forget (anchoredAdd (anchoredMul x y) (anchoredMul x z))) := by
  have hL : SurrealCore.PreGame.toIGame (forget (anchoredMul x (anchoredAdd y z))) = 0 := by
    exact forget_toIGame_mul_nullCut_left x (anchoredAdd y z) hx
  have hR1 : SurrealCore.PreGame.toIGame (forget (anchoredMul x y)) = 0 := by
    exact forget_toIGame_mul_nullCut_left x y hx
  have hR2 : SurrealCore.PreGame.toIGame (forget (anchoredMul x z)) = 0 := by
    exact forget_toIGame_mul_nullCut_left x z hx
  calc
    SurrealCore.PreGame.toIGame (forget (anchoredMul x (anchoredAdd y z))) = 0 := hL
    _ = SurrealCore.PreGame.toIGame (forget (anchoredAdd (anchoredMul x y) (anchoredMul x z))) := by
          calc
            (0 : IGame) =
                SurrealCore.PreGame.toIGame (forget (anchoredMul x y)) +
                  SurrealCore.PreGame.toIGame (forget (anchoredMul x z)) := by
                    rw [hR1, hR2]
                    simp
            _ = SurrealCore.PreGame.toIGame
                  (forget (anchoredAdd (anchoredMul x y) (anchoredMul x z))) := by
                    symm
                    exact forget_toIGame_add (anchoredMul x y) (anchoredMul x z)

/-- Anchored right distributive zero-fragment through forgetful semantics. -/
theorem forget_toIGame_mul_add_nullCut_right
    (x y z : AnchoredPreGame) (hz : forget z = SurrealCore.nullCut) :
    SurrealCore.PreGame.toIGame (forget (anchoredMul (anchoredAdd x y) z)) =
      SurrealCore.PreGame.toIGame
        (forget (anchoredAdd (anchoredMul x z) (anchoredMul y z))) := by
  have hL : SurrealCore.PreGame.toIGame (forget (anchoredMul (anchoredAdd x y) z)) = 0 := by
    exact forget_toIGame_mul_nullCut_right (anchoredAdd x y) z hz
  have hR1 : SurrealCore.PreGame.toIGame (forget (anchoredMul x z)) = 0 := by
    exact forget_toIGame_mul_nullCut_right x z hz
  have hR2 : SurrealCore.PreGame.toIGame (forget (anchoredMul y z)) = 0 := by
    exact forget_toIGame_mul_nullCut_right y z hz
  calc
    SurrealCore.PreGame.toIGame (forget (anchoredMul (anchoredAdd x y) z)) = 0 := hL
    _ = SurrealCore.PreGame.toIGame
          (forget (anchoredAdd (anchoredMul x z) (anchoredMul y z))) := by
          calc
            (0 : IGame) =
                SurrealCore.PreGame.toIGame (forget (anchoredMul x z)) +
                  SurrealCore.PreGame.toIGame (forget (anchoredMul y z)) := by
                    rw [hR1, hR2]
                    simp
            _ = SurrealCore.PreGame.toIGame
                  (forget (anchoredAdd (anchoredMul x z) (anchoredMul y z))) := by
                    symm
                    exact forget_toIGame_add (anchoredMul x z) (anchoredMul y z)

end Surreal
end Numbers
end HeytingLean
