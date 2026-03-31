import Mathlib
import HeytingLean.PDE.Certificates.SchauderGate

namespace HeytingLean.PDE.Automation

lemma ratNatPosOfTwoLe {n : Nat} (h : 2 ≤ n) : (0 : Rat) < n := by
  have hn : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) h
  exact_mod_cast hn

lemma oneLtOneAddDivNat {α : Rat} {n : Nat} (hα : 0 < α) (hn : 0 < n) :
    (1 : Rat) < 1 + α / (n : Rat) := by
  have hnRat : (0 : Rat) < (n : Rat) := by exact_mod_cast hn
  have hDiv : (0 : Rat) < α / (n : Rat) := div_pos hα hnRat
  linarith

lemma mulLtOfDivLt {p q r : Rat} (hp : 0 < p) (h : q / p < r) : q < p * r := by
  have h' : q < r * p := (div_lt_iff₀ hp).1 h
  simpa [mul_comm, mul_left_comm, mul_assoc] using h'

lemma gateIneqToMulForm {n : Nat} {p q α : Rat} (hp : 0 < p)
    (h : q / p < 1 + α / (n : Rat)) : q < p * (1 + α / (n : Rat)) := by
  exact mulLtOfDivLt hp h

end HeytingLean.PDE.Automation
