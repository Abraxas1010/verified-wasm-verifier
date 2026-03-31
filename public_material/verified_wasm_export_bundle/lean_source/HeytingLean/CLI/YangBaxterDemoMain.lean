import Mathlib.Data.Matrix.Basic

/-!
# Yang–Baxter gate demo (Kauffman Phase 4, toy)

This executable checks a classic Kauffman–Lomonaco-style 2-qubit braiding operator `R`
at the **integer-matrix** level:

* `R` satisfies the Yang–Baxter (braid) equation on 3 qubits:
  `(R₁₂)(R₂₃)(R₁₂) = (R₂₃)(R₁₂)(R₂₃)`.
* `Rᵀ R = 2·I`, i.e. after scaling by `1/√2` it becomes orthogonal/unitary (over ℝ/ℂ).

We keep the check fully finite and executable: all matrices are 8×8 or smaller with entries in `ℤ`.
-/

namespace HeytingLean.CLI.YangBaxterDemoMain

open Matrix

abbrev Mat (n : Nat) := Matrix (Fin n) (Fin n) Int

private def join2 (a b : Fin 2) : Fin 4 :=
  ⟨a.1 * 2 + b.1, by
    have ha : a.1 ≤ 1 := Nat.le_of_lt_succ a.2
    have hb : b.1 ≤ 1 := Nat.le_of_lt_succ b.2
    have : a.1 * 2 + b.1 ≤ 1 * 2 + 1 := Nat.add_le_add (Nat.mul_le_mul_right 2 ha) hb
    exact lt_of_le_of_lt this (by decide : 3 < 4)⟩

private def split3 (i : Fin 8) : Fin 2 × Fin 2 × Fin 2 :=
  (Fin.ofNat 2 (i.1 / 4), Fin.ofNat 2 (i.1 / 2), Fin.ofNat 2 i.1)

private def split4 (i : Fin 16) : Fin 2 × Fin 2 × Fin 2 × Fin 2 :=
  (Fin.ofNat 2 (i.1 / 8), Fin.ofNat 2 (i.1 / 4), Fin.ofNat 2 (i.1 / 2), Fin.ofNat 2 i.1)

private def R : Mat 4 :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => 1
    | 0, 3 => 1
    | 1, 1 => 1
    | 1, 2 => -1
    | 2, 1 => 1
    | 2, 2 => 1
    | 3, 0 => -1
    | 3, 3 => 1
    | _, _ => 0

private def R12 : Mat 8 :=
  fun i j =>
    let (a', b', c') := split3 i
    let (a, b, c) := split3 j
    if c' = c then
      R (join2 a' b') (join2 a b)
    else
      0

private def R23 : Mat 8 :=
  fun i j =>
    let (a', b', c') := split3 i
    let (a, b, c) := split3 j
    if a' = a then
      R (join2 b' c') (join2 b c)
    else
      0

private def R12_4 : Mat 16 :=
  fun i j =>
    let (a', b', c', d') := split4 i
    let (a, b, c, d) := split4 j
    if c' = c ∧ d' = d then
      R (join2 a' b') (join2 a b)
    else
      0

private def R23_4 : Mat 16 :=
  fun i j =>
    let (a', b', c', d') := split4 i
    let (a, b, c, d) := split4 j
    if a' = a ∧ d' = d then
      R (join2 b' c') (join2 b c)
    else
      0

private def R34_4 : Mat 16 :=
  fun i j =>
    let (a', b', c', d') := split4 i
    let (a, b, c, d) := split4 j
    if a' = a ∧ b' = b then
      R (join2 c' d') (join2 c d)
    else
      0

private def die (msg : String) : IO UInt32 := do
  IO.eprintln msg
  pure 1

private def ok (b : Bool) (msg : String) : IO Unit := do
  if !b then
    throw (IO.userError msg)

def main (_argv : List String) : IO UInt32 := do
  try
    let lhs : Mat 8 := (R12 * R23) * R12
    let rhs : Mat 8 := (R23 * R12) * R23
    ok (decide (lhs = rhs)) "Yang–Baxter equation failed for R"

    let ortho : Mat 4 := (R.transpose) * R
    let rhsOrtho : Mat 4 := (2 : Int) • (1 : Mat 4)
    ok (decide (ortho = rhsOrtho)) "Orthogonality-up-to-scale check failed: RᵀR ≠ 2·I"

    -- 4-qubit locality checks: braid relation on (2,3,4) and disjoint commutation of (1,2) with (3,4).
    let lhs4 : Mat 16 := (R23_4 * R34_4) * R23_4
    let rhs4 : Mat 16 := (R34_4 * R23_4) * R34_4
    ok (decide (lhs4 = rhs4)) "Yang–Baxter failed for 4-qubit lift (R23/R34)"

    let comm4L : Mat 16 := R12_4 * R34_4
    let comm4R : Mat 16 := R34_4 * R12_4
    ok (decide (comm4L = comm4R)) "Disjoint commutation failed: R12*R34 ≠ R34*R12"

    IO.println "yang_baxter_demo: ok"
    pure 0
  catch e =>
    die s!"yang_baxter_demo: FAILED: {e}"

end HeytingLean.CLI.YangBaxterDemoMain

open HeytingLean.CLI.YangBaxterDemoMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.YangBaxterDemoMain.main args
