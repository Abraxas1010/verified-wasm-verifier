import HeytingLean.Numbers.Surreal.Operations

namespace HeytingLean
namespace Numbers
namespace Surreal

/-!
  Normalized Surreals: a thin wrapper around `Game` that fixes a
  canonical representative via `normalize`. We use this to stage
  algebraic structure where laws hold by construction modulo normalization.
-/

noncomputable section

/-- A game is normalized when `normalize g = g`. -/
def IsNorm (g : Game) : Prop := normalize g = g

/-- Subtype of normalized games. -/
def NormGame := { g : Game // IsNorm g }

namespace NormGame

/-- Project any game to its normalized representative. -/
def ofGame (g : Game) : NormGame :=
  ⟨normalize g, by
    have := normalize_idem g
    simpa [IsNorm] using this⟩

/-- Underlying game of a normalized game. -/
def val (x : NormGame) : Game := x.1

@[simp] lemma val_mk (g : Game) (h : IsNorm g) : val ⟨g, h⟩ = g := rfl

@[simp] lemma val_ofGame (g : Game) : val (ofGame g) = normalize g := rfl

@[simp] lemma isNorm_val (x : NormGame) : IsNorm (val x) := x.2

/-- Coe to the underlying game. -/
instance : Coe NormGame Game where
  coe := val

/-! Zero and operations -/

/-- Zero as a normalized game. -/
def zeroN : NormGame := ofGame zero

/-- Addition on normalized games: normalize after Conway addition. -/
def addN (x y : NormGame) : NormGame :=
  ofGame (addConway x.1 y.1)

/-- Multiplication on normalized games: normalize after Conway multiplication. -/
def mulN (x y : NormGame) : NormGame :=
  ofGame (mulConway x.1 y.1)

/-! Basic laws inherited from normalized Game lemmas -/

@[simp] lemma zero_val : (zeroN).1 = normalize zero := rfl

@[simp] lemma add_val (x y : NormGame) : (addN x y).1 = normalize (addConway x.1 y.1) := rfl

@[simp] lemma mul_val (x y : NormGame) : (mulN x y).1 = normalize (mulConway x.1 y.1) := rfl

/-- Zero is a left identity for addition on normalized games. -/
theorem zero_add (x : NormGame) : addN zeroN x = x := by
  apply Subtype.ext
  calc
    (addN zeroN x).1 = normalize (addConway zero x.1) := rfl
    _ = normalize x.1 := normalize_add_zero_left x.1
    _ = x.1 := x.2

/-- Zero is a right identity for addition on normalized games. -/
theorem add_zero (x : NormGame) : addN x zeroN = x := by
  apply Subtype.ext
  calc
    (addN x zeroN).1 = normalize (addConway x.1 zero) := rfl
    _ = normalize x.1 := normalize_add_zero_right x.1
    _ = x.1 := x.2

/-- Zero annihilates multiplication on the left. -/
theorem zero_mul (x : NormGame) : mulN zeroN x = zeroN := by
  apply Subtype.ext
  calc
    (mulN zeroN x).1 = normalize (mulConway zero x.1) := rfl
    _ = normalize zero := normalize_mul_zero_left x.1
    _ = zeroN.1 := by rfl

/-- Zero annihilates multiplication on the right. -/
theorem mul_zero (x : NormGame) : mulN x zeroN = zeroN := by
  apply Subtype.ext
  calc
    (mulN x zeroN).1 = normalize (mulConway x.1 zero) := rfl
    _ = normalize zero := normalize_mul_zero_right x.1
    _ = zeroN.1 := by rfl

end NormGame

end

end Surreal
end Numbers
end HeytingLean
