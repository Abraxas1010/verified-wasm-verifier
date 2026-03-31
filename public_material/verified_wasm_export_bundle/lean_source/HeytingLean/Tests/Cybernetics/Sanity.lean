import HeytingLean.Cybernetics.Observer
import HeytingLean.Cybernetics.Feedback
import HeytingLean.Cybernetics.Viability

/-
Compile-only sanity for SOC scaffold: parity observer and simple feedback.
-/

namespace HeytingLean
namespace Tests
namespace Cybernetics

open HeytingLean.Cybernetics

def parityObs : Observer Bool Nat :=
  { observe := fun n => n % 2 = 0 }

def incIfTrue : Feedback Nat Bool :=
  { step := fun s o => if o then s + 1 else s }

def once : Nat := Feedback.loop parityObs incIfTrue 3

/-- Closed loop preserves the trivial predicate `λ _, True` for the
`parityObs` / `incIfTrue` pair. -/
def closedLoop_trivial_viable :
    ∀ _s : Nat, True → True :=
  HeytingLean.Cybernetics.preserves_closedLoopStep
    (O := parityObs) (F := incIfTrue) (P := fun _ : Nat => True)
    (h := by intro _ _; trivial)

-- Nontrivial predicate preserved by a different feedback
def stayIfTrue : Feedback Nat Bool :=
  { step := fun s o => if o then s else s + 1 }

/-- Closed loop preserves evenness under the `stayIfTrue` feedback. -/
def closedLoop_even_viable :
    ∀ s, s % 2 = 0 →
      (HeytingLean.Cybernetics.closedLoopStep parityObs stayIfTrue s) % 2 = 0 := by
  intro s hs
  -- P(s) := even s; for even s, `stayIfTrue` leaves s unchanged.
  have hstep : ∀ t, t % 2 = 0 →
      (stayIfTrue.step t (parityObs.observe t)) % 2 = 0 := by
    intro t ht
    simp [stayIfTrue, parityObs, ht]
  -- Use the generic closed-loop preservation lemma.
  have h :=
    HeytingLean.Cybernetics.preserves_closedLoopStep
      (O := parityObs) (F := stayIfTrue)
      (P := fun t : Nat => t % 2 = 0)
      (h := by intro t ht; exact hstep t ht)
  simpa [HeytingLean.Cybernetics.closedLoopStep] using h s hs

end Cybernetics
end Tests
end HeytingLean
