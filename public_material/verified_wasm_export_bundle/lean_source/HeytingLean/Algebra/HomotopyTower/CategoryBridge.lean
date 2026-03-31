import Mathlib.CategoryTheory.Groupoid.Discrete
import HeytingLean.Algebra.HomotopyTower.Stabilization
import HeytingLean.LoF.Combinators.Category.OmegaTowerLimit

namespace HeytingLean
namespace Algebra
namespace HomotopyTower

open CategoryTheory
open HeytingLean.LoF.Combinators.Category

universe u

variable {α : Type u} [Order.Frame α]

/-- Stagewise fixed points of the nucleus tower. -/
abbrev FixedPointCarrier (T : NucleusTower (α := α)) (n : Nat) : Type u :=
  {x : α // T.level n x = x}

/-- The discrete category on the stagewise fixed points. -/
abbrev FixedPointObj (T : NucleusTower (α := α)) (n : Nat) : Type u :=
  Discrete (FixedPointCarrier T n)

/-- A fixed point at stage `n+1` is automatically a fixed point at stage `n`. -/
def dropFixedPoint (T : NucleusTower (α := α)) (n : Nat) :
    FixedPointCarrier T (n + 1) → FixedPointCarrier T n := by
  intro x
  exact ⟨x.1, fixed_eq_of_le (T.mono (Nat.le_succ n)) x.2⟩

/-- The stage-drop functor between discrete fixed-point categories. -/
def dropFunctor (T : NucleusTower (α := α)) (n : Nat) :
    FixedPointObj T (n + 1) ⥤ FixedPointObj T n :=
  Discrete.functor (fun x => Discrete.mk (dropFixedPoint T n x))

/-- The discrete fixed-point tower associated to a nucleus tower. -/
def fixedPointCatTower (T : NucleusTower (α := α)) : CatTower where
  Obj := FixedPointObj T
  inst := fun _ => by infer_instance
  drop := dropFunctor T

/-- The stabilized fixed-point object at the chosen stabilization stage. -/
abbrev StableFixedPointObject (T : NucleusTower (α := α)) (hfin : FiniteImage T) : Type u :=
  FixedPointCarrier T (stabilizationIndex T hfin)

def stableFixedPointAt (T : NucleusTower (α := α)) (hfin : FiniteImage T)
    (x : StableFixedPointObject T hfin) (n : Nat) : FixedPointCarrier T n := by
  refine ⟨x.1, ?_⟩
  by_cases hn : n ≤ stabilizationIndex T hfin
  · exact fixed_eq_of_le (T.mono hn) x.2
  · have hsn : stabilizationIndex T hfin ≤ n := Nat.le_of_not_ge hn
    calc
      T.level n x.1 = T.level (stabilizationIndex T hfin) x.1 := by
        simpa using congrArg (fun J : Nucleus α => J x.1)
          ((stabilizationIndex_spec T hfin) n hsn)
      _ = x.1 := x.2

/-- A stabilized fixed point determines a compatible object in the tower limit. -/
def stableObjectToTowerLimit (T : NucleusTower (α := α)) (hfin : FiniteImage T) :
    StableFixedPointObject T hfin → TowerLimit (fixedPointCatTower T) := by
  intro x
  refine
    { obj := fun n => Discrete.mk (stableFixedPointAt T hfin x n)
      compat := ?_ }
  intro n
  change Discrete.mk (dropFixedPoint T n (stableFixedPointAt T hfin x (n + 1))) =
    Discrete.mk (stableFixedPointAt T hfin x n)
  apply congrArg Discrete.mk
  apply Subtype.ext
  rfl

/-- The stabilized fixed-point stage as a discrete category. -/
abbrev StableFixedPointCategory (T : NucleusTower (α := α)) (hfin : FiniteImage T) : Type u :=
  Discrete (StableFixedPointObject T hfin)

/-- Discrete functor from stabilized fixed points into the fixed-point tower limit. -/
def stableObjectFunctor (T : NucleusTower (α := α)) (hfin : FiniteImage T) :
    StableFixedPointCategory T hfin ⥤ TowerLimit (fixedPointCatTower T) :=
  Discrete.functor (stableObjectToTowerLimit T hfin)

/-- Adjacent stages in a compatible tower family have the same underlying carrier value. -/
theorem towerLimit_val_eq_succ (T : NucleusTower (α := α))
    (X : TowerLimit (fixedPointCatTower T)) (n : Nat) :
    ((X.obj (n + 1)).as).1 = (X.obj n).as.1 := by
  have h := congrArg (fun Z => Z.as.1) (X.compat n)
  simpa [dropFunctor, dropFixedPoint] using h

/-- Any two stages in a compatible tower family have the same underlying carrier value. -/
theorem towerLimit_val_eq_of_le (T : NucleusTower (α := α))
    (X : TowerLimit (fixedPointCatTower T)) {n m : Nat} (h : n ≤ m) :
    ((X.obj m).as).1 = (X.obj n).as.1 := by
  induction h with
  | refl => rfl
  | @step m h ih =>
      exact (towerLimit_val_eq_succ T X m).trans ih

/-- Evaluate a compatible tower family at the stabilization stage. -/
noncomputable def towerLimitToStableObject (T : NucleusTower (α := α)) (hfin : FiniteImage T) :
    TowerLimit (fixedPointCatTower T) → StableFixedPointObject T hfin :=
  fun X => (X.obj (stabilizationIndex T hfin)).as

/-- The stabilized stage and the fixed-point tower limit carry the same discrete data. -/
noncomputable def stableObjectEquivType (T : NucleusTower (α := α)) (hfin : FiniteImage T) :
    StableFixedPointObject T hfin ≃ TowerLimit (fixedPointCatTower T) where
  toFun := stableObjectToTowerLimit T hfin
  invFun := towerLimitToStableObject T hfin
  left_inv x := by
    rfl
  right_inv X := by
    apply TowerLimit.ext
    intro n
    apply congrArg Discrete.mk
    apply Subtype.ext
    dsimp [towerLimitToStableObject, stableObjectToTowerLimit, stableFixedPointAt]
    by_cases hn : n ≤ stabilizationIndex T hfin
    · exact towerLimit_val_eq_of_le T X hn
    · exact (towerLimit_val_eq_of_le T X (Nat.le_of_not_ge hn)).symm

instance towerLimitFixedPointHomSubsingleton (T : NucleusTower (α := α))
    (X Y : TowerLimit (fixedPointCatTower T)) : Subsingleton (X ⟶ Y) := by
  refine ⟨?_⟩
  intro f g
  apply TowerLimit.Hom.ext
  intro n
  letI : Subsingleton (X.obj n ⟶ Y.obj n) := by
    cases X.obj n
    cases Y.obj n
    change Subsingleton (ULift (PLift (_ = _)))
    infer_instance
  exact Subsingleton.elim _ _

/-- The fixed-point tower limit is discrete: any morphism forces equality of objects. -/
theorem towerLimitFixedPoint_eq_of_hom (T : NucleusTower (α := α))
    {X Y : TowerLimit (fixedPointCatTower T)} (f : X ⟶ Y) : X = Y := by
  apply TowerLimit.ext
  intro n
  apply congrArg Discrete.mk
  exact Discrete.eq_of_hom (f.app n)

/-- The actual tower-limit category of fixed points is equivalent to the corresponding discrete category. -/
noncomputable def towerLimitDiscreteEquivalence (T : NucleusTower (α := α)) :
    Discrete (TowerLimit (fixedPointCatTower T)) ≌ TowerLimit (fixedPointCatTower T) where
  functor := Discrete.functor id
  inverse :=
    { obj := Discrete.mk
      map := by
        intro X Y f
        exact Discrete.eqToHom (towerLimitFixedPoint_eq_of_hom T f) }
  unitIso :=
    Discrete.natIso fun X => eqToIso (by simp)
  counitIso :=
    NatIso.ofComponents (fun X => eqToIso (towerLimitFixedPoint_eq_of_hom T (𝟙 X))) (by
      intro X Y f
      apply Subsingleton.elim)

/-- The stabilized fixed-point category is equivalent to the inverse limit of the fixed-point tower. -/
noncomputable def stableObjectEquivalence (T : NucleusTower (α := α)) (hfin : FiniteImage T) :
    StableFixedPointCategory T hfin ≌ TowerLimit (fixedPointCatTower T) :=
  (Discrete.equivalence (stableObjectEquivType T hfin)).trans (towerLimitDiscreteEquivalence T)

end HomotopyTower
end Algebra
end HeytingLean
