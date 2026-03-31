import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic
import HeytingLean.CodingTheory.Hamming.Basic

namespace HeytingLean
namespace CodingTheory
namespace Hamming

/-!
# Hamming (7,4) code (standard parity-check form)
-/

abbrev BitVec7 := BitVec 7
abbrev BitVec4 := BitVec 4

def hamming74 (x : BitVec7) : Prop :=
  x ⟨0, by decide⟩ + x ⟨2, by decide⟩ + x ⟨4, by decide⟩ + x ⟨6, by decide⟩ = 0 ∧
  x ⟨1, by decide⟩ + x ⟨2, by decide⟩ + x ⟨5, by decide⟩ + x ⟨6, by decide⟩ = 0 ∧
  x ⟨3, by decide⟩ + x ⟨4, by decide⟩ + x ⟨5, by decide⟩ + x ⟨6, by decide⟩ = 0

def hamming74Syndrome (x : BitVec7) : BitVec 3 := fun
  | ⟨0, _⟩ => x ⟨0, by decide⟩ + x ⟨2, by decide⟩ + x ⟨4, by decide⟩ + x ⟨6, by decide⟩
  | ⟨1, _⟩ => x ⟨1, by decide⟩ + x ⟨2, by decide⟩ + x ⟨5, by decide⟩ + x ⟨6, by decide⟩
  | ⟨2, _⟩ => x ⟨3, by decide⟩ + x ⟨4, by decide⟩ + x ⟨5, by decide⟩ + x ⟨6, by decide⟩

def hamming74Encode (m : BitVec4) : BitVec7 := by
  classical
  let d0 := m ⟨0, by decide⟩
  let d1 := m ⟨1, by decide⟩
  let d2 := m ⟨2, by decide⟩
  let d3 := m ⟨3, by decide⟩
  let p1 : Bit := d0 + d1 + d3
  let p2 : Bit := d0 + d2 + d3
  let p4 : Bit := d1 + d2 + d3
  exact fun i =>
    match i.1 with
    | 0 => p1
    | 1 => p2
    | 2 => d0
    | 3 => p4
    | 4 => d1
    | 5 => d2
    | _ => d3

def flipBit {n : Nat} (x : BitVec n) (i : Fin n) : BitVec n :=
  fun j => if j = i then x j + 1 else x j

def syndromeToIndex (s : BitVec 3) : Option (Fin 7) := by
  classical
  let b0 := bitToNat (s ⟨0, by decide⟩)
  let b1 := bitToNat (s ⟨1, by decide⟩)
  let b2 := bitToNat (s ⟨2, by decide⟩)
  let idx : Nat := b0 + 2 * b1 + 4 * b2
  if h0 : idx = 0 then
    exact none
  else
    let pos := idx - 1
    if hlt : pos < 7 then
      exact some ⟨pos, hlt⟩
    else
      exact none

def syndromeOfIndex : Fin 7 → BitVec 3
| ⟨0, _⟩ => fun | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 0 | ⟨2, _⟩ => 0
| ⟨1, _⟩ => fun | ⟨0, _⟩ => 0 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => 0
| ⟨2, _⟩ => fun | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => 0
| ⟨3, _⟩ => fun | ⟨0, _⟩ => 0 | ⟨1, _⟩ => 0 | ⟨2, _⟩ => 1
| ⟨4, _⟩ => fun | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 0 | ⟨2, _⟩ => 1
| ⟨5, _⟩ => fun | ⟨0, _⟩ => 0 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => 1
| ⟨_, _⟩ => fun | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => 1

def hamming74Decode (x : BitVec7) : BitVec7 :=
  match syndromeToIndex (hamming74Syndrome x) with
  | none => x
  | some i => flipBit x i

def hamming74Message (x : BitVec7) : BitVec4 :=
  fun
  | ⟨0, _⟩ => x ⟨2, by decide⟩
  | ⟨1, _⟩ => x ⟨4, by decide⟩
  | ⟨2, _⟩ => x ⟨5, by decide⟩
  | ⟨3, _⟩ => x ⟨6, by decide⟩

lemma syndromeToIndex_syndromeOfIndex (i : Fin 7) :
    syndromeToIndex (syndromeOfIndex i) = some i := by
  classical
  fin_cases i <;> simp [syndromeOfIndex, syndromeToIndex, bitToNat]

lemma hamming74Syndrome_flip_encode (m : BitVec4) (i : Fin 7) :
    hamming74Syndrome (flipBit (hamming74Encode m) i) = syndromeOfIndex i := by
  revert m i
  native_decide

lemma flipBit_involutive {n : Nat} (x : BitVec n) (i : Fin n) :
    flipBit (flipBit x i) i = x := by
  funext j
  by_cases h : j = i
  · simp [flipBit, h, bit_add_one_add_one]
  · simp [flipBit, h]

lemma exists_flipBit_of_hammingDist_eq_one {n : Nat} (x y : BitVec n)
    (h : hammingDist x y = 1) : ∃ i, y = flipBit x i := by
  classical
  set s : Finset (Fin n) := Finset.univ.filter fun i => x i ≠ y i
  have hs_card : s.card = 1 := by
    simpa [hammingDist, s] using h
  obtain ⟨i, hs⟩ := Finset.card_eq_one.mp hs_card
  have hi : x i ≠ y i := by
    have : i ∈ s := by simp [hs]
    simpa [s] using this
  have hneq : ∀ j, j ≠ i → x j = y j := by
    intro j hj
    have : j ∉ s := by
      by_contra hmem
      have : j = i := by
        have : j ∈ ({i} : Finset (Fin n)) := by simpa [hs] using hmem
        simpa [Finset.mem_singleton] using this
      exact (hj this).elim
    have : ¬ x j ≠ y j := by
      simpa [s] using this
    exact not_ne_iff.mp this
  refine ⟨i, ?_⟩
  funext j
  by_cases hji : j = i
  · subst j
    have : y i = x i + 1 := (bit_ne_iff_add_one_eq (x i) (y i)).1 hi
    simpa [flipBit] using this
  · have hxy : x j = y j := hneq j hji
    simp [flipBit, hji, hxy]

lemma syndromeToIndex_zero : syndromeToIndex (fun _ : Fin 3 => (0 : Bit)) = none := by
  simp [syndromeToIndex]

lemma hamming74Syndrome_of_codeword (x : BitVec7) (hx : hamming74 x) :
    hamming74Syndrome x = 0 := by
  funext k
  fin_cases k
  · simpa [hamming74Syndrome] using hx.1
  · simpa [hamming74Syndrome] using hx.2.1
  · simpa [hamming74Syndrome] using hx.2.2

lemma hamming74Syndrome_encode (m : BitVec4) :
    hamming74Syndrome (hamming74Encode m) = 0 := by
  revert m
  native_decide

lemma hamming74Encode_mem (m : BitVec4) : hamming74 (hamming74Encode m) := by
  have hs : hamming74Syndrome (hamming74Encode m) = 0 := hamming74Syndrome_encode m
  have h0 :
      hamming74Encode m ⟨0, by decide⟩ + hamming74Encode m ⟨2, by decide⟩ +
        hamming74Encode m ⟨4, by decide⟩ + hamming74Encode m ⟨6, by decide⟩ = 0 := by
    have := congrArg (fun f => f ⟨0, by decide⟩) hs
    simpa [hamming74Syndrome] using this
  have h1 :
      hamming74Encode m ⟨1, by decide⟩ + hamming74Encode m ⟨2, by decide⟩ +
        hamming74Encode m ⟨5, by decide⟩ + hamming74Encode m ⟨6, by decide⟩ = 0 := by
    have := congrArg (fun f => f ⟨1, by decide⟩) hs
    simpa [hamming74Syndrome] using this
  have h2 :
      hamming74Encode m ⟨3, by decide⟩ + hamming74Encode m ⟨4, by decide⟩ +
        hamming74Encode m ⟨5, by decide⟩ + hamming74Encode m ⟨6, by decide⟩ = 0 := by
    have := congrArg (fun f => f ⟨2, by decide⟩) hs
    simpa [hamming74Syndrome] using this
  exact And.intro h0 (And.intro h1 h2)

lemma hamming74Decode_of_zero_syndrome (x : BitVec7)
    (h : hamming74Syndrome x = 0) : hamming74Decode x = x := by
  have hz : syndromeToIndex (hamming74Syndrome x) = none := by
    simpa [h] using (syndromeToIndex_zero)
  simp [hamming74Decode, hz]

lemma hamming74Decode_of_codeword (x : BitVec7) (hx : hamming74 x) :
    hamming74Decode x = x := by
  apply hamming74Decode_of_zero_syndrome
  exact hamming74Syndrome_of_codeword x hx

lemma hamming74Decode_encode (m : BitVec4) :
    hamming74Decode (hamming74Encode m) = hamming74Encode m := by
  apply hamming74Decode_of_zero_syndrome
  simpa using (hamming74Syndrome_encode m)

lemma hamming74Decode_corrects_single_error (m : BitVec4) (i : Fin 7) :
    hamming74Decode (flipBit (hamming74Encode m) i) = hamming74Encode m := by
  have hsyn :
      syndromeToIndex (hamming74Syndrome (flipBit (hamming74Encode m) i)) = some i := by
    have hs := hamming74Syndrome_flip_encode m i
    simpa [hs] using (syndromeToIndex_syndromeOfIndex i)
  simp [hamming74Decode, hsyn, flipBit_involutive]

lemma hamming74Message_encode (m : BitVec4) :
    hamming74Message (hamming74Encode m) = m := by
  classical
  funext i
  fin_cases i <;> simp [hamming74Message, hamming74Encode]

lemma hamming74Encode_message_of_codeword (x : BitVec7) (hx : hamming74 x) :
    hamming74Encode (hamming74Message x) = x := by
  classical
  funext i
  fin_cases i
  ·
    set d0 := x ⟨2, by decide⟩
    set d1 := x ⟨4, by decide⟩
    set d3 := x ⟨6, by decide⟩
    have h' :
        x ⟨0, by decide⟩ + (d0 + d1 + d3) = 0 := by
      simpa [hamming74Message, d0, d1, d3, add_assoc] using hx.1
    have h'' : x ⟨0, by decide⟩ = -(d0 + d1 + d3) :=
      (eq_neg_iff_add_eq_zero).2 h'
    have h0 : x ⟨0, by decide⟩ = d0 + d1 + d3 := by
      simpa [add_assoc, add_comm, add_left_comm] using h''
    simpa [hamming74Encode, hamming74Message, d0, d1, d3, add_assoc, add_comm, add_left_comm] using h0.symm
  ·
    set d0 := x ⟨2, by decide⟩
    set d2 := x ⟨5, by decide⟩
    set d3 := x ⟨6, by decide⟩
    have h' :
        x ⟨1, by decide⟩ + (d0 + d2 + d3) = 0 := by
      simpa [hamming74Message, d0, d2, d3, add_assoc] using hx.2.1
    have h'' : x ⟨1, by decide⟩ = -(d0 + d2 + d3) :=
      (eq_neg_iff_add_eq_zero).2 h'
    have h1 : x ⟨1, by decide⟩ = d0 + d2 + d3 := by
      simpa [add_assoc, add_comm, add_left_comm] using h''
    simpa [hamming74Encode, hamming74Message, d0, d2, d3, add_assoc, add_comm, add_left_comm] using h1.symm
  · simp [hamming74Encode, hamming74Message]
  ·
    set d1 := x ⟨4, by decide⟩
    set d2 := x ⟨5, by decide⟩
    set d3 := x ⟨6, by decide⟩
    have h' :
        x ⟨3, by decide⟩ + (d1 + d2 + d3) = 0 := by
      simpa [hamming74Message, d1, d2, d3, add_assoc] using hx.2.2
    have h'' : x ⟨3, by decide⟩ = -(d1 + d2 + d3) :=
      (eq_neg_iff_add_eq_zero).2 h'
    have h3 : x ⟨3, by decide⟩ = d1 + d2 + d3 := by
      simpa [add_assoc, add_comm, add_left_comm] using h''
    simpa [hamming74Encode, hamming74Message, d1, d2, d3, add_assoc, add_comm, add_left_comm] using h3.symm
  · simp [hamming74Encode, hamming74Message]
  · simp [hamming74Encode, hamming74Message]
  · simp [hamming74Encode, hamming74Message]

lemma hamming74Decode_corrects_single_error_codeword (x : BitVec7) (hx : hamming74 x) (i : Fin 7) :
    hamming74Decode (flipBit x i) = x := by
  have hx' : hamming74Encode (hamming74Message x) = x :=
    hamming74Encode_message_of_codeword x hx
  simpa [hx'] using
    (hamming74Decode_corrects_single_error (m := hamming74Message x) i)

lemma hamming74Decode_corrects_dist_one (x y : BitVec7) (hx : hamming74 x)
    (h : hammingDist x y ≤ 1) : hamming74Decode y = x := by
  classical
  have hcases : hammingDist x y = 0 ∨ hammingDist x y = 1 :=
    Nat.le_one_iff_eq_zero_or_eq_one.mp h
  cases hcases with
  | inl h0 =>
      have hxy : x = y := (_root_.hammingDist_eq_zero).1 h0
      simpa [hxy] using (hamming74Decode_of_codeword x hx)
  | inr h1 =>
      obtain ⟨i, hy⟩ := exists_flipBit_of_hammingDist_eq_one (x := x) (y := y) h1
      simpa [hy] using (hamming74Decode_corrects_single_error_codeword x hx i)

end Hamming
end CodingTheory
end HeytingLean
