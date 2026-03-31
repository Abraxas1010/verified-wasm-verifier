import HeytingLean.CategoryTheory.Monad.Basic
import HeytingLean.Core.Nucleus
import HeytingLean.Topos.JRatchet

namespace HeytingLean
namespace CategoryTheory
namespace Monad

variable {L : Type*} [SemilatticeInf L] [OrderBot L]

theorem nucleus_idempotent_bridge (N : Core.Nucleus L) (x : L) :
    N.R (N.R x) = N.R x :=
  N.idempotent x

theorem ratchet_trajectory_closed_under_id (level : Nat → Nat)
    (hmono : Topos.JRatchet.RatchetTrajectory level) :
    Topos.JRatchet.RatchetTrajectory (fun n => id (level n)) := by
  intro a b hab
  simpa using hmono a b hab

end Monad
end CategoryTheory
end HeytingLean
