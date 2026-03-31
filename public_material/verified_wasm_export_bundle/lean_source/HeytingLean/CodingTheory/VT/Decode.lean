import Mathlib.Data.List.Basic
import Mathlib.Tactic
import HeytingLean.CodingTheory.VT.Basic

namespace HeytingLean
namespace CodingTheory
namespace VT

/-!
# VT decoding (specification-level)

We model decoding for a single deletion using existence/uniqueness.
This is a specification-level decoder: it returns the unique codeword,
if it exists, and otherwise fails.
-/

def SingleDel (x y : List Bit) : Prop :=
  ∃ i, i < x.length ∧ y = sDel x i

noncomputable def vtDecode (n a m : Nat) (y : List Bit) : Option (List Bit) := by
  classical
  by_cases h : ∃! x, x ∈ vtCode n a m ∧ SingleDel x y
  · exact some (Classical.choose h)
  · exact none

lemma vtDecode_spec {n a m : Nat} {y : List Bit}
    (h : ∃! x, x ∈ vtCode n a m ∧ SingleDel x y) :
    vtDecode n a m y = some (Classical.choose h) := by
  classical
  simp [vtDecode, h]

lemma vtDecode_correct {n a m : Nat} {x y : List Bit}
    (hx : x ∈ vtCode n a m) (hdel : SingleDel x y)
    (huniq : ∀ x', x' ∈ vtCode n a m → SingleDel x' y → x' = x) :
    vtDecode n a m y = some x := by
  classical
  have h : ∃! x, x ∈ vtCode n a m ∧ SingleDel x y := by
    refine ⟨x, ⟨hx, hdel⟩, ?_⟩
    intro x' hx'
    exact huniq x' hx'.1 hx'.2
  have hxchoose : Classical.choose h = x := by
    have hspec : Classical.choose h ∈ vtCode n a m ∧ SingleDel (Classical.choose h) y :=
      (Classical.choose_spec h).1
    exact huniq _ hspec.1 hspec.2
  unfold vtDecode
  rw [dif_pos h]
  exact congrArg some hxchoose

end VT
end CodingTheory
end HeytingLean
