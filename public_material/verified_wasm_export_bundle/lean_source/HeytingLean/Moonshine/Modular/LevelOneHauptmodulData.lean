import HeytingLean.Moonshine.Hauptmodul
import HeytingLean.Moonshine.Modular.Hauptmodul
import HeytingLean.Moonshine.Modular.JSeries
import HeytingLean.Moonshine.Modular.JInvariant

set_option autoImplicit false

noncomputable section

namespace HeytingLean.Moonshine.Modular

/--
Concrete level-1 Hauptmodul package used by the Moonshine statement layer.

The `q`-expansion slot is `J_q`, and the genus-zero slot records the established
analytic-side level-1 Hauptmodul predicate for `kleinJ₀`.
-/
def kleinJ₀_levelOneHauptmodulData (G : Type*) [Group G] :
    HeytingLean.Moonshine.HauptmodulData G where
  Γ := (⊤ : Subgroup HeytingLean.Moonshine.SL2Z)
  qExp := J_q
  genusZero := IsHauptmodul (⊤ : Subgroup SL2Z) kleinJ₀

theorem kleinJ₀_levelOneHauptmodulData_genusZero (G : Type*) [Group G] :
    (kleinJ₀_levelOneHauptmodulData (G := G)).genusZero :=
  kleinJ₀_isHauptmodul

theorem kleinJ₀_levelOneHauptmodulData_qExp (G : Type*) [Group G] :
    (kleinJ₀_levelOneHauptmodulData (G := G)).qExp = J_q :=
  rfl

end HeytingLean.Moonshine.Modular
