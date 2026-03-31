import HeytingLean.PerspectivalPlenum.ReReentryTower

namespace HeytingLean
namespace Tests
namespace PerspectivalPlenum

universe u

variable {α : Type u} [Order.Frame α]
variable (S T : HeytingLean.PerspectivalPlenum.RatchetStep α)
variable (J : Nucleus α)

#check HeytingLean.PerspectivalPlenum.RatchetCompatibility
#check HeytingLean.PerspectivalPlenum.RatchetStep.iterate
#check HeytingLean.PerspectivalPlenum.RatchetStep.compose
#check HeytingLean.PerspectivalPlenum.RatchetTower
#check HeytingLean.PerspectivalPlenum.RatchetTower.stratify

example :
    HeytingLean.PerspectivalPlenum.RatchetStep.iterate S 2 J
      = HeytingLean.PerspectivalPlenum.RatchetStep.iterate S 1 J := by
  exact HeytingLean.PerspectivalPlenum.RatchetStep.iterate_two_eq_one (S := S) (J := J)

example (h : HeytingLean.PerspectivalPlenum.RatchetCompatibility S T) :
    (HeytingLean.PerspectivalPlenum.RatchetStep.compose S T h) J = S (T J) := by
  rfl

end PerspectivalPlenum
end Tests
end HeytingLean
