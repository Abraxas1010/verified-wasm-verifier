import HeytingLean.Crypto.KEM.MLKEM203Params

/-!
# ML-KEM parameter search/selection (small verified helper)

This module provides a tiny, deterministic "suggest parameters" helper over the *standard*
ML-KEM FIPS 203 bundles:

- `mlkem512`, `mlkem768`, `mlkem1024`.

It is intentionally conservative: it only filters by:
1) the bundle validity predicate (`validParams`),
2) a coarse security level target, and
3) a maximum ciphertext size.

This is a *utility layer*, not a cryptographic proof.
-/

namespace HeytingLean
namespace Crypto
namespace KEM
namespace FIPS203

open scoped BigOperators

/-- NIST security level targets. -/
inductive SecurityLevel
  | cat1
  | cat3
  | cat5
  deriving Repr, DecidableEq

/-- Coarse estimated security bits keyed by `k` (spec narrative only). -/
def estimatedBitSecurity (k : Nat) : Nat :=
  match k with
  | 2 => 128
  | 3 => 192
  | 4 => 256
  | _ => 0

private def requiredBits (level : SecurityLevel) : Nat :=
  match level with
  | .cat1 => 128
  | .cat3 => 192
  | .cat5 => 256

/-- Check if parameters meet the requested coarse security level (as a proposition). -/
def meetsSecurityLevel (p : MLKEM203Params) (level : SecurityLevel) : Prop :=
  requiredBits level ≤ estimatedBitSecurity p.k

instance (p : MLKEM203Params) (level : SecurityLevel) : Decidable (meetsSecurityLevel p level) := by
  unfold meetsSecurityLevel
  infer_instance

def candidates : List MLKEM203Params :=
  [mlkem512, mlkem768, mlkem1024]

private def findFirst? (xs : List α) (pred : α → Prop) [DecidablePred pred] : Option α :=
  match xs with
  | [] => none
  | x :: xs => if pred x then some x else findFirst? xs pred

private theorem findFirst?_some {xs : List α} {pred : α → Prop} [DecidablePred pred] {a : α} :
    findFirst? xs pred = some a → pred a := by
  induction xs with
  | nil =>
      intro h
      simp [findFirst?] at h
  | cons x xs ih =>
      intro h
      by_cases hx : pred x
      · -- the head is chosen
        simp [findFirst?, hx] at h
        cases h
        exact hx
      · -- search continues in the tail
        simp [findFirst?, hx] at h
        exact ih h

/-- Suggest a parameter set, preferring smaller sets, subject to ciphertext size and validity. -/
def suggestParams (level : SecurityLevel) (maxCtSize : Nat) : Option MLKEM203Params :=
  findFirst? candidates fun p => meetsSecurityLevel p level ∧ validParams p ∧ p.ctSize ≤ maxCtSize

theorem suggestParams_sound (level : SecurityLevel) (maxCt : Nat) (p : MLKEM203Params)
    (h : suggestParams level maxCt = some p) :
    validParams p ∧ meetsSecurityLevel p level ∧ p.ctSize ≤ maxCt := by
  classical
  have hp :
      meetsSecurityLevel p level ∧ validParams p ∧ p.ctSize ≤ maxCt := by
    -- The found element satisfies the predicate by construction.
    exact findFirst?_some (xs := candidates) (pred := fun p => meetsSecurityLevel p level ∧ validParams p ∧ p.ctSize ≤ maxCt) h
  exact ⟨hp.2.1, hp.1, hp.2.2⟩

end FIPS203
end KEM
end Crypto
end HeytingLean
