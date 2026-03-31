import HeytingLean.Moonshine.Monster.Spec
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false

namespace HeytingLean.Moonshine

namespace MonsterSpec

variable (S : MonsterSpec)

instance : Group S.M := S.instGroup
instance : Fintype S.M := S.instFintype

lemma finite : Finite S.M := by
  classical
  infer_instance

lemma simple : IsSimpleGroup S.M :=
  S.isSimple

lemma card : Fintype.card S.M = monsterOrder :=
  S.card_eq

lemma center : Subgroup.center S.M = ⊥ :=
  S.center_trivial

end MonsterSpec

end HeytingLean.Moonshine
