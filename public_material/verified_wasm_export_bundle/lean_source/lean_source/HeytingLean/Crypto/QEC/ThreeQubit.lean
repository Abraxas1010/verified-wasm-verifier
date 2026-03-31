import Mathlib.Tactic
import HeytingLean.Crypto.QEC.Stabilizer

/-!
# Three-qubit repetition (bit-flip) code

We model a minimal “stabilizer code” over the discrete state space `Fin 3 → Bool`.

The code space is the set of 3-bit strings with all bits equal (`000` or `111`), presented as the
intersection of two parity constraints:
- bit0 = bit1
- bit1 = bit2

We then show that majority decoding corrects any single bit-flip error on a codeword.
-/

namespace HeytingLean
namespace Crypto
namespace QEC
namespace ThreeQubit

open HeytingLean.Crypto.QEC

abbrev Bit3 := Fin 3 → Bool

namespace Bit3

/-- Flip a bit at index `i`. -/
def flipAt (i : Fin 3) (x : Bit3) : Bit3 :=
  fun j => if j = i then !x j else x j

theorem flipAt_self (i : Fin 3) (x : Bit3) : flipAt i x i = !x i := by
  simp [flipAt]

theorem flipAt_ne (i j : Fin 3) (x : Bit3) (h : j ≠ i) : flipAt i x j = x j := by
  simp [flipAt, h]

end Bit3

/-! ## Stabilizer-code presentation -/

/-- Two parity-check generators for the repetition code. -/
inductive Gen where
  | eq01
  | eq12

/-- Constraint predicate for a generator. -/
def good : Gen → Set Bit3
  | Gen.eq01 => {x | x ⟨0, by decide⟩ = x ⟨1, by decide⟩}
  | Gen.eq12 => {x | x ⟨1, by decide⟩ = x ⟨2, by decide⟩}

/-- The repetition code as a stabilizer code (constraints-only). -/
def code : StabilizerCode Bit3 where
  Gen := Gen
  good := good

/-- Boolean message bit encoded as a length-3 constant word. -/
def encode (b : Bool) : Bit3 :=
  fun _ => b

theorem encode_mem_codeSpace (b : Bool) : encode b ∈ code.codeSpace := by
  intro g
  cases g <;> simp [code, good, encode]

/-- Majority of three bits (true if at least two are true). -/
def majority (x : Bit3) : Bool :=
  decide ((Nat.succ (Nat.succ 0)) ≤
    ((if x ⟨0, by decide⟩ then 1 else 0) +
     (if x ⟨1, by decide⟩ then 1 else 0) +
     (if x ⟨2, by decide⟩ then 1 else 0)))

theorem majority_encode (b : Bool) : majority (encode b) = b := by
  cases b <;> decide

/-- Majority decoding. -/
def decode (x : Bit3) : Bool :=
  majority x

theorem decode_encode (b : Bool) : decode (encode b) = b := by
  simpa [decode] using majority_encode b

/-! ## Single-bit-flip correction -/

theorem decode_flipAt_encode (i : Fin 3) (b : Bool) :
    decode (Bit3.flipAt i (encode b)) = b := by
  fin_cases i <;> cases b <;> decide

end ThreeQubit
end QEC
end Crypto
end HeytingLean
