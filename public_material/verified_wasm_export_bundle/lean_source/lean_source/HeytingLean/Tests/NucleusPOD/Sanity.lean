import HeytingLean.NucleusPOD

namespace HeytingLean
namespace Tests
namespace NucleusPOD

open HeytingLean.NucleusPOD

example :
    swarmToposWitness.topology = swarmTopology ∧
    (∀ A, swarmToposWitness.topology.covers A (fun _ => True)) ∧
    (∀ A, Ω A = true ∨ Ω A = false) := by
  simpa using swarm_topos

example {A B C D : Agent}
    (f : Channel A B) (g : Channel B C) (h : Channel C D) :
    Channel.compose (Channel.compose f g) h = Channel.compose f (Channel.compose g h) := by
  exact category_assoc f g h

example (a b : Nat) : j (Nat.min a b) = Nat.min (j a) (j b) := by
  simpa using lt_meet a b

example (P Q : Presheaf) :
    (∀ A, closure (Q A) = Q A) →
    ((∀ A, sheafify P A ≤ Q A) ↔ (∀ A, P A ≤ includeSheaf Q A)) := by
  intro hQ
  simpa using sheafification_left_adjoint P Q hQ

end NucleusPOD
end Tests
end HeytingLean
