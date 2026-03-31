import HeytingLean.Numbers.Surreal.GameN
import HeytingLean.Numbers.Surreal.Operations

open HeytingLean.Numbers
open HeytingLean.Numbers.Surreal

/-! Smoke tests for Conway ops (negation). -/

-- zero/neg basics
#check Surreal.zero
#check Surreal.neg
#check Surreal.negN
-- canonical short games
#check Surreal.one
-- Euler-style symmetric cut (expository): `{−1|1}` corresponds to `mkGame [zero] [one]`
#check Surreal.mkGame [Surreal.zero] [Surreal.one]

-- simp checks
example : Surreal.neg Surreal.zero = Surreal.zero := by
  simp

def gOneN : Surreal.GameN 1 :=
  Surreal.GameN.succ (n := 0) [⟨0, Surreal.GameN.mk0⟩] []

example :
    Surreal.negN gOneN = Surreal.GameN.succ (n := 0) [] [⟨0, Surreal.GameN.mk0⟩] := by
  rfl

example : Surreal.negN (Surreal.negN gOneN) = gOneN := by
  simp [gOneN]

example (g : Sigma Surreal.GameN) (h : g ≠ Surreal.zero) :
    Surreal.neg g =
      Surreal.ofPreGame (HeytingLean.Numbers.SurrealCore.neg (Surreal.toPreGame g)) := by
  simpa using Surreal.Lemmas.neg_def_nonzero (g := g) h

-- addition skeleton checks
#check Surreal.add
#check Surreal.addConway
#check Surreal.mul
example (x : Sigma Surreal.GameN) : Surreal.addConway Surreal.zero x = x := by
  simpa using Surreal.addConway_zero_left x
example (x : Sigma Surreal.GameN) : Surreal.addConway x Surreal.zero = x := by
  simpa using Surreal.addConway_zero_right x
noncomputable section
  open Surreal
  -- Conway multiplication checks
  #check Surreal.mulConway
  example : Surreal.mulConway Surreal.zero Surreal.zero = Surreal.zero := by
    simp
  example (x : Sigma Surreal.GameN) : Surreal.mulConway x Surreal.zero = Surreal.zero := by
    simp
  example (y : Sigma Surreal.GameN) : Surreal.mulConway Surreal.zero y = Surreal.zero := by
    simp
  -- shape lemmas for zero factor
  example (y : Sigma Surreal.GameN) : (Surreal.mulConway Surreal.zero y).L = [] := by
    simp
  example (y : Sigma Surreal.GameN) : (Surreal.mulConway Surreal.zero y).R = [] := by
    simp
end

#check Surreal.LmulLL_zero_left
#check Surreal.LmulLL_zero_right
#check Surreal.LmulRR_zero_left
#check Surreal.LmulRR_zero_right
#check Surreal.RmulLR_zero_left
#check Surreal.RmulLR_zero_right
#check Surreal.RmulRL_zero_left
#check Surreal.RmulRL_zero_right

/-! Normalization checks -/

noncomputable section
  open Surreal
  #check Surreal.normalize
  example : Surreal.normalize Surreal.zero = Surreal.zero := by
    simp
  example (x : Sigma Surreal.GameN)
      (hL : Surreal.Game.L x = []) (hR : Surreal.Game.R x = []) :
      Surreal.normalize x = Surreal.zero := by
    simpa using Surreal.normalize_terminal x hL hR
  example (x : Sigma Surreal.GameN)
      (h : Surreal.Game.L x ≠ [] ∨ Surreal.Game.R x ≠ []) :
      Surreal.normalize x = x := by
    simpa using Surreal.normalize_nonterminal x h
  example (x : Sigma Surreal.GameN) :
      Surreal.normalize (Surreal.normalize x) = Surreal.normalize x := by
    simpa using Surreal.normalize_idem x
  example (y : Sigma Surreal.GameN) :
      Surreal.normalize (Surreal.addConway Surreal.zero y) =
      Surreal.normalize y := by
    simpa using Surreal.normalize_add_zero_left y
  example (x : Sigma Surreal.GameN) :
      Surreal.normalize (Surreal.addConway x Surreal.zero) =
      Surreal.normalize x := by
    simpa using Surreal.normalize_add_zero_right x
  /-! Normalization is a canonical closure (idempotent). -/
  example (x y : Sigma Surreal.GameN) :
      Surreal.normalize
          (Surreal.normalize (Surreal.addConway x y)) =
      Surreal.normalize (Surreal.addConway x y) := by
    simpa using Surreal.normalize_idem (Surreal.addConway x y)
  example (x y : Sigma Surreal.GameN) :
      Surreal.normalize
          (Surreal.addConway Surreal.zero (Surreal.addConway x y)) =
      Surreal.normalize (Surreal.addConway x y) := by
    simpa using
      Surreal.normalize_add_zero_left (Surreal.addConway x y)
  example (x y : Sigma Surreal.GameN) :
      Surreal.normalize
          (Surreal.addConway (Surreal.addConway x y) Surreal.zero) =
      Surreal.normalize (Surreal.addConway x y) := by
    simpa using
      Surreal.normalize_add_zero_right (Surreal.addConway x y)
  example (x : Sigma Surreal.GameN) :
      Surreal.normalize (Surreal.mulConway Surreal.zero x) =
      Surreal.normalize Surreal.zero := by
    simpa using Surreal.normalize_mul_zero_left x
  example (x : Sigma Surreal.GameN) :
      Surreal.normalize (Surreal.mulConway x Surreal.zero) =
      Surreal.normalize Surreal.zero := by
    simpa using Surreal.normalize_mul_zero_right x
end

/-! mkGame and addition/multiplication shape API checks -/

#check Surreal.mkGame
#check Surreal.day_mkGame
#check Surreal.day_mkGame_nonempty
#check Surreal.L_mkGame_nonempty
#check Surreal.R_mkGame_nonempty

#check Surreal.L_addConway
#check Surreal.R_addConway
#check Surreal.L_mulConway
#check Surreal.R_mulConway
#check Surreal.LmulLL
#check Surreal.LmulRR
#check Surreal.RmulLR
#check Surreal.RmulRL

example (x y l : Sigma Surreal.GameN) (hl : l ∈ (Surreal.addConway x y).L) :
    l.fst < (Surreal.addConway x y).fst := by
  exact Surreal.L_addConway x y l hl

example (x y r : Sigma Surreal.GameN) (hr : r ∈ (Surreal.addConway x y).R) :
    r.fst < (Surreal.addConway x y).fst := by
  exact Surreal.R_addConway x y r hr

example (L R : List (Sigma Surreal.GameN))
    (h : L ≠ [] ∨ R ≠ [])
    (l : Sigma Surreal.GameN) (hl : l ∈ (Surreal.mkGame L R).L) :
    l.fst < (Surreal.mkGame L R).fst := by
  exact Surreal.L_mkGame_nonempty h l hl

example (L R : List (Sigma Surreal.GameN))
    (h : L ≠ [] ∨ R ≠ [])
    (r : Sigma Surreal.GameN) (hr : r ∈ (Surreal.mkGame L R).R) :
    r.fst < (Surreal.mkGame L R).fst := by
  exact Surreal.R_mkGame_nonempty h r hr

example : (Surreal.add Surreal.zero Surreal.zero).fst = 0 := by
  simp [Surreal.add, Surreal.mkGame_nil_nil]

example : (Surreal.addConway Surreal.zero Surreal.zero).fst = 0 := by
  simp [Surreal.addConway]

example : (Surreal.mul Surreal.zero Surreal.zero).fst = 0 := by
  simp [Surreal.mul, Surreal.mkGame_nil_nil]
