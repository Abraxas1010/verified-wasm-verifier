import HeytingLean.CategoryTheory.Monad.Bridge

namespace HeytingLean
namespace Bridges
namespace Archetype

variable {L : Type*} [SemilatticeInf L] [OrderBot L]

theorem monad_to_nucleus_idempotence (N : Core.Nucleus L) (x : L) :
    N.R (N.R x) = N.R x := by
  simpa using CategoryTheory.Monad.nucleus_idempotent_bridge N x

theorem monad_to_nucleus_extensive (N : Core.Nucleus L) (x : L) :
    x ≤ N.R x := by
  exact N.extensive x

end Archetype
end Bridges
end HeytingLean
