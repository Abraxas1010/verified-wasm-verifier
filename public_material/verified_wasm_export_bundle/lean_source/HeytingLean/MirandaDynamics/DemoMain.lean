import HeytingLean.MirandaDynamics

/-!
# MirandaDynamics demo executable

This is a tiny runtime demo that exercises the *computable* parts of the MirandaDynamics spine:

- reaching relation composition,
- “union nucleus” closure on decidable sets.

It performs no file IO and should not crash under hostile env/PATH tests.
-/

namespace HeytingLean
namespace MirandaDynamics

namespace Demo

open TKFT
open FixedPoint

def succRel : TKFT.ReachingRel Nat Nat :=
  ⟨fun a b => b = a + 1⟩

def succ2Rel : TKFT.ReachingRel Nat Nat :=
  TKFT.ReachingRel.comp succRel succRel

theorem succ2Rel_spec (a b : Nat) : succ2Rel.rel a b ↔ b = a + 2 := by
  constructor
  · rintro ⟨m, hm1, hm2⟩
    -- hm1 : m = a+1, hm2 : b = m+1
    rcases hm1 with rfl
    -- b = (a+1)+1 = a+2
    simpa [Nat.add_assoc] using hm2
  · intro hb
    refine ⟨a + 1, rfl, ?_⟩
    -- b = (a+1)+1
    simpa [Nat.add_assoc] using hb

def main (_argv : List String) : IO UInt32 := do
  IO.println "[miranda_dynamics_demo] TKFT reaching-rel composition"
  let a := 40
  let b := 42
  -- `succ2Rel.rel a b` is defined via an ∃-witness, so it is not decidable in general.
  -- Instead, we print the decidable RHS of the proved equivalence `succ2Rel_spec`.
  IO.println s!"[demo] succ2Rel_spec: {a} ↝ {b} iff {b} = {a} + 2; RHS evaluates to {decide (b = a + 2)}"

  IO.println "[miranda_dynamics_demo] union-nucleus closure (decidable Set Nat)"
  -- Membership in `close(S)=S∪U` is decidable here because we use equality predicates.
  IO.println s!"[demo] 0 ∈ close(S)? {decide ((0 : Nat) = 0 ∨ (0 : Nat) = 1)}"
  IO.println s!"[demo] 1 ∈ close(S)? {decide ((1 : Nat) = 0 ∨ (1 : Nat) = 1)}"
  IO.println s!"[demo] 2 ∈ close(S)? {decide ((2 : Nat) = 0 ∨ (2 : Nat) = 1)}"

  return 0

end Demo

end MirandaDynamics
end HeytingLean

def main (args : List String) : IO UInt32 :=
  HeytingLean.MirandaDynamics.Demo.main args
