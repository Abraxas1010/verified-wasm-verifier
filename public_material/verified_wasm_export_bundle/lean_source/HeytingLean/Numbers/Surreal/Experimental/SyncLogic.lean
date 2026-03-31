import HeytingLean.Numbers.Surreal.Tactics
import HeytingLean.Numbers.Surreal.Experimental.KinematicForcing

namespace HeytingLean
namespace Numbers
namespace Surreal
namespace Experimental

open Lean Elab Tactic

/-- Irreducibility certificate used by sync fallback reasoning. -/
def irreducibleCertificate (budget : Nat) (w v : KinematicWorld) : Prop :=
  horizonCertificate budget w v

@[simp] theorem irreducibleCertificate_implies_unobtainable
    {budget : Nat} {w v : KinematicWorld}
    (h : irreducibleCertificate budget w v) :
    unobtainable budget w v :=
  horizonCertificate_implies_unobtainable h

/-- Horizon-aware simplification fallback for synchronization goals. -/
macro "sync_logic" : tactic =>
  `(tactic| first
      | (simp [
          irreducibleCertificate,
          horizonCertificate,
          horizon,
          unobtainable,
          irreducibleCertificate_implies_unobtainable
        ] ; done)
      | (noneist_simp; done)
      | (surreal_simp; done)
      | (simp; done))

end Experimental
end Surreal
end Numbers
end HeytingLean
