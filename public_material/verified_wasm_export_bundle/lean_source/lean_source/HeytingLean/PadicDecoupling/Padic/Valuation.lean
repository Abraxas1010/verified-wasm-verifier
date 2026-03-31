import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.NumberTheory.Padics.RingHoms

namespace HeytingLean.PadicDecoupling.Padic

open padicNorm

variable (p : ℕ) [Fact p.Prime]

theorem padic_norm_sum_le_max (q r : ℚ) :
    padicNorm p (q + r) ≤ max (padicNorm p q) (padicNorm p r) :=
  padicNorm.nonarchimedean

theorem padic_norm_sub_le_max (q r : ℚ) :
    padicNorm p (q - r) ≤ max (padicNorm p q) (padicNorm p r) :=
  padicNorm.sub

theorem appr_lt_pow (x : ℤ_[p]) (k : ℕ) :
    x.appr k < p ^ k :=
  PadicInt.appr_lt x k

end HeytingLean.PadicDecoupling.Padic
