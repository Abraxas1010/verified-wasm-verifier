import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay
import HeytingLean.Epiplexity.Crypto.Axioms

namespace HeytingLean
namespace Epiplexity
namespace Crypto

universe u

open scoped BigOperators

noncomputable section

open HeytingLean.Probability.InfoTheory
open HeytingLean.Security.Model.Computational

namespace FinDist

variable {α : Type u} [Fintype α]

theorem map_id (P : FinDist α) : map (f := fun a : α => a) P = P := by
  classical
  ext a
  simp [map]

end FinDist

theorem negligible_zero : Negligible (0 : Nat → ℝ) := by
  unfold Negligible
  exact Asymptotics.superpolynomialDecay_zero Filter.atTop (fun n : Nat => (n : ℝ))

/-!
Bridge wrappers: the Epiplexity crypto predicates are finite and explicit; this file records the
standard “ε is negligible” packaging relative to `Security.Model.Computational.Negligible`.
-/

def CSPRNGSecureNegligible (k n T : Nat) (G : BitStr k → BitStr n) : Prop :=
  ∃ ε : Nat → ℝ, Negligible ε ∧ CSPRNGSecure k n T G ε

theorem csprngSecureNegligible_of {k n T : Nat} {G : BitStr k → BitStr n} {ε : Nat → ℝ}
    (h : CSPRNGSecure k n T G ε) (hε : Negligible ε) : CSPRNGSecureNegligible k n T G :=
  ⟨ε, hε, h⟩

/-!
Toy witnesses (consistency checks).

These are not intended as cryptographic claims; they are sanity checks that the predicate layer is
nonempty and interoperates with the negligible-function wrapper.
-/

theorem csprngSecure_id (n T : Nat) :
    CSPRNGSecure (k := n) (n := n) T (fun x : BitStr n => x) (0 : Nat → ℝ) := by
  intro D _hDT
  have hmap :
      FinDist.map (f := fun x : BitStr n => x) (Epiplexity.FinDist.uniform (α := BitStr n))
        = Epiplexity.FinDist.uniform (α := BitStr n) :=
    FinDist.map_id (P := (Epiplexity.FinDist.uniform (α := BitStr n)))
  simp [hmap, advantage]

theorem csprngSecureNegligible_id (n T : Nat) :
    CSPRNGSecureNegligible (k := n) (n := n) T (fun x : BitStr n => x) := by
  refine ⟨(0 : Nat → ℝ), negligible_zero, csprngSecure_id (n := n) (T := T)⟩

end

end Crypto
end Epiplexity
end HeytingLean
