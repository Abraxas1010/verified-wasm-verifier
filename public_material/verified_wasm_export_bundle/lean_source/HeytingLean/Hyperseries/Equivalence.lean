import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Logic.Hydra
import Mathlib.SetTheory.Surreal.Multiplication
import HeytingLean.Hyperseries.Eval
import HeytingLean.Hyperseries.BridgePilot
import HeytingLean.Hyperseries.Description

set_option linter.deprecated.module false

namespace HeytingLean
namespace Hyperseries

section GeneralTransport

variable {K : Type*} [CommRing K] [HyperserialDescription K]

/-- Transport ring structure from `K` to its canonical hyperserial descriptions. -/
noncomputable instance : CommRing (HDesc K) :=
  (HyperserialDescription.equiv (K := K)).commRing

/-- Realization as a ring equivalence. -/
noncomputable def evalRingEquiv : HDesc K ≃+* K :=
  (HyperserialDescription.equiv (K := K)).ringEquiv

/-- Realization as a ring homomorphism. -/
noncomputable def evalRingHom : HDesc K →+* K :=
  (evalRingEquiv (K := K)).toRingHom

@[simp] theorem evalRingHom_apply (h : HDesc K) :
    evalRingHom (K := K) h = HyperserialDescription.realize (K := K) h := by
  rfl

end GeneralTransport

section SurrealSpecialization

variable [HyperserialDescription Surreal]

/-- Hyperseries specialized to surreals. -/
abbrev HSNo : Type* := HDesc Surreal

/-- Evaluation at surreal `ω` (once a description interface is provided). -/
noncomputable def evalOmega : HSNo →+* Surreal :=
  evalRingHom (K := Surreal)

/-- Distinguished symbol corresponding to surreal `ω`. -/
noncomputable def X : HSNo :=
  HyperserialDescription.describe (K := Surreal) omegaSurreal

@[simp] theorem evalOmega_X : evalOmega X = omegaSurreal := by
  simp [evalOmega, X]

/-- Existence and uniqueness of a hyperserial description for each surreal. -/
theorem existsUnique_hyperseries (a : Surreal) : ∃! h : HSNo, evalOmega h = a := by
  simpa [HSNo, evalOmega] using (HyperserialDescription.existsUnique (K := Surreal) a)

section PilotBridge

abbrev PilotSeries := HeytingLean.Numbers.Surreal.Hyperseries.Series

/--
Canonical hyperserial description obtained by evaluating an integer-lane DSL
expression in a chosen surreal exp/log semantics package.
-/
noncomputable def describeExprWith (S : SurrealExpLogSemantics) (e : HExpr) : HSNo :=
  HyperserialDescription.describe (K := Surreal) (HExpr.eval (SurrealExpLogSemantics.toModel S) e)

@[simp] theorem evalOmega_describeExprWith (S : SurrealExpLogSemantics) (e : HExpr) :
    evalOmega (describeExprWith S e) = HExpr.eval (SurrealExpLogSemantics.toModel S) e := by
  simp [describeExprWith, evalOmega]

/-- Canonical hyperserial description obtained by evaluating an integer-lane DSL expression. -/
noncomputable def describeExpr (e : HExpr) : HSNo :=
  describeExprWith surrealSemanticsDefault e

theorem describeExpr_eq_describeExprWith_default (e : HExpr) :
    describeExpr e = describeExprWith surrealSemanticsDefault e := by
  rfl

/--
Bool-selector specialization of `describeExprWith`:
`false` follows the default lane, `true` follows the nontrivial lane.
-/
noncomputable def describeExprSelect (useNontrivial : Bool) (e : HExpr) : HSNo :=
  describeExprWith (surrealSemantics useNontrivial) e

theorem describeExprSelect_false (e : HExpr) :
    describeExprSelect false e = describeExpr e := by
  rfl

@[simp] theorem evalOmega_describeExprSelect (useNontrivial : Bool) (e : HExpr) :
    evalOmega (describeExprSelect useNontrivial e) =
      HExpr.eval (surrealModelWith useNontrivial) e := by
  simp [describeExprSelect, surrealModelWith, surrealSemantics]

@[simp] theorem evalOmega_describeExpr (e : HExpr) :
    evalOmega (describeExpr e) = HExpr.eval surrealModel e := by
  calc
    evalOmega (describeExpr e) =
        HExpr.eval (SurrealExpLogSemantics.toModel surrealSemanticsDefault) e := by
      change evalOmega (describeExprWith surrealSemanticsDefault e) =
        HExpr.eval (SurrealExpLogSemantics.toModel surrealSemanticsDefault) e
      exact evalOmega_describeExprWith surrealSemanticsDefault e
    _ = HExpr.eval surrealModel e := by
      rfl

/-- Canonical hyperserial description attached to a pilot series in semantics package `S`. -/
noncomputable def ofPilotSeriesWith (S : SurrealExpLogSemantics) (s : PilotSeries) : HSNo :=
  describeExprWith S (BridgePilot.ofSeries.{0} s)

theorem evalOmega_ofPilotSeriesWith (S : SurrealExpLogSemantics) (s : PilotSeries) :
    evalOmega (ofPilotSeriesWith S s) =
      HExpr.eval (SurrealExpLogSemantics.toModel S) (BridgePilot.ofSeries.{0} s) := by
  unfold ofPilotSeriesWith describeExprWith
  simp [evalOmega, evalRingHom_apply]

/-- Canonical hyperserial description attached to a pilot finite-support series. -/
noncomputable def ofPilotSeries (s : PilotSeries) : HSNo :=
  ofPilotSeriesWith surrealSemanticsDefault s

theorem ofPilotSeries_eq_ofPilotSeriesWith_default (s : PilotSeries) :
    ofPilotSeries s = ofPilotSeriesWith surrealSemanticsDefault s := by
  rfl

/--
Bool-selector specialization of `ofPilotSeriesWith`:
`false` follows the default lane, `true` follows the nontrivial lane.
-/
noncomputable def ofPilotSeriesSelect (useNontrivial : Bool) (s : PilotSeries) : HSNo :=
  ofPilotSeriesWith (surrealSemantics useNontrivial) s

theorem ofPilotSeriesSelect_false (s : PilotSeries) :
    ofPilotSeriesSelect false s = ofPilotSeries s := by
  rfl

theorem evalOmega_ofPilotSeriesSelect (useNontrivial : Bool) (s : PilotSeries) :
    evalOmega (ofPilotSeriesSelect useNontrivial s) =
      HExpr.eval (surrealModelWith useNontrivial) (BridgePilot.ofSeries.{0} s) := by
  simp [ofPilotSeriesSelect, surrealModelWith, surrealSemantics, evalOmega_ofPilotSeriesWith]

theorem evalOmega_ofPilotSeries (s : PilotSeries) :
    evalOmega (ofPilotSeries s) = HExpr.eval surrealModel (BridgePilot.ofSeries.{0} s) := by
  simpa [ofPilotSeries, surrealModel, instHyperserialModelSurreal, surrealSemanticsDefault] using
    (evalOmega_ofPilotSeriesWith surrealSemanticsDefault s)

theorem evalOmega_ofPilotSeriesWith_append (S : SurrealExpLogSemantics) (x y : PilotSeries) :
    evalOmega (ofPilotSeriesWith S (x ++ y)) =
      evalOmega (ofPilotSeriesWith S x) + evalOmega (ofPilotSeriesWith S y) := by
  rw [evalOmega_ofPilotSeriesWith, evalOmega_ofPilotSeriesWith, evalOmega_ofPilotSeriesWith]
  exact BridgePilot.eval_ofPilot_append.{_, 0} (M := SurrealExpLogSemantics.toModel S) x y

theorem evalOmega_ofPilotSeriesWith_normalize (S : SurrealExpLogSemantics) (s : PilotSeries) :
    evalOmega (ofPilotSeriesWith S (HeytingLean.Numbers.Surreal.Hyperseries.normalize s)) =
      evalOmega (ofPilotSeriesWith S s) := by
  rw [evalOmega_ofPilotSeriesWith, evalOmega_ofPilotSeriesWith]
  exact BridgePilot.eval_ofPilot_normalize.{_, 0} (M := SurrealExpLogSemantics.toModel S) s

theorem evalOmega_ofPilotSeriesWith_mul_monomial (S : SurrealExpLogSemantics)
    (c₁ c₂ : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    evalOmega
        (ofPilotSeriesWith S
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₁ e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₂ e₂))) =
      evalOmega
        (ofPilotSeriesWith S
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial (c₁ * c₂) (e₁ + e₂))) := by
  rw [evalOmega_ofPilotSeriesWith, evalOmega_ofPilotSeriesWith]
  exact BridgePilot.eval_ofSeries_mul_monomial.{_, 0}
    (M := SurrealExpLogSemantics.toModel S) c₁ c₂ e₁ e₂

theorem evalOmega_ofPilotSeriesWith_monomial_zero (S : SurrealExpLogSemantics)
    (e : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    evalOmega (ofPilotSeriesWith S (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e)) = 0 := by
  rw [evalOmega_ofPilotSeriesWith]
  rw [BridgePilot.eval_ofSeries_monomial (M := SurrealExpLogSemantics.toModel S) 0 e]
  simp

@[simp] theorem ofPilotSeries_nil :
    ofPilotSeries ([] : PilotSeries) = 0 := by
  have hReal :
      HyperserialDescription.realize (K := Surreal) (ofPilotSeries ([] : PilotSeries)) =
        HyperserialDescription.realize (K := Surreal) (0 : HSNo) := by
    change evalOmega (ofPilotSeries ([] : PilotSeries)) = evalOmega (0 : HSNo)
    rw [evalOmega_ofPilotSeries]
    simp
  exact HyperserialDescription.ext (K := Surreal) hReal

theorem evalOmega_ofPilotSeries_append (x y : PilotSeries) :
    evalOmega (ofPilotSeries (x ++ y)) =
      evalOmega (ofPilotSeries x) + evalOmega (ofPilotSeries y) := by
  simpa [ofPilotSeries] using
    (evalOmega_ofPilotSeriesWith_append surrealSemanticsDefault x y)

theorem ofPilotSeries_append (x y : PilotSeries) :
    ofPilotSeries (x ++ y) = ofPilotSeries x + ofPilotSeries y := by
  have hReal :
      HyperserialDescription.realize (K := Surreal) (ofPilotSeries (x ++ y)) =
        HyperserialDescription.realize (K := Surreal) (ofPilotSeries x + ofPilotSeries y) := by
    change evalOmega (ofPilotSeries (x ++ y)) = evalOmega (ofPilotSeries x + ofPilotSeries y)
    simpa [map_add] using (evalOmega_ofPilotSeries_append x y)
  exact HyperserialDescription.ext (K := Surreal) hReal

theorem ofPilotSeries_add (x y : PilotSeries) :
    ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add x y) =
      ofPilotSeries x + ofPilotSeries y := by
  simpa [HeytingLean.Numbers.Surreal.Hyperseries.add] using (ofPilotSeries_append x y)

@[simp] theorem ofPilotSeries_append_nil (x : PilotSeries) :
    ofPilotSeries (x ++ []) = ofPilotSeries x := by
  simp

@[simp] theorem ofPilotSeries_nil_append (x : PilotSeries) :
    ofPilotSeries ([] ++ x) = ofPilotSeries x := by
  simp

theorem ofPilotSeries_append_assoc (x y z : PilotSeries) :
    ofPilotSeries ((x ++ y) ++ z) =
      ofPilotSeries x + ofPilotSeries y + ofPilotSeries z := by
  rw [ofPilotSeries_append, ofPilotSeries_append]

@[simp] theorem ofPilotSeries_add_nil (x : PilotSeries) :
    ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add x []) = ofPilotSeries x := by
  simp [HeytingLean.Numbers.Surreal.Hyperseries.add]

@[simp] theorem ofPilotSeries_nil_add (x : PilotSeries) :
    ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add [] x) = ofPilotSeries x := by
  simp [HeytingLean.Numbers.Surreal.Hyperseries.add]

theorem ofPilotSeries_add_assoc (x y z : PilotSeries) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.add x y) z) =
      ofPilotSeries x + ofPilotSeries y + ofPilotSeries z := by
  simpa [HeytingLean.Numbers.Surreal.Hyperseries.add, List.append_assoc, add_assoc] using
    (ofPilotSeries_append_assoc x y z)

theorem ofPilotSeries_add_comm (x y : PilotSeries) :
    ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add x y) =
      ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add y x) := by
  simp [ofPilotSeries_add, add_comm]

@[simp] theorem evalOmega_ofPilotSeries_append_nil (x : PilotSeries) :
    evalOmega (ofPilotSeries (x ++ [])) = evalOmega (ofPilotSeries x) := by
  exact congrArg evalOmega (ofPilotSeries_append_nil x)

@[simp] theorem evalOmega_ofPilotSeries_nil_append (x : PilotSeries) :
    evalOmega (ofPilotSeries ([] ++ x)) = evalOmega (ofPilotSeries x) := by
  exact congrArg evalOmega (ofPilotSeries_nil_append x)

theorem evalOmega_ofPilotSeries_append_assoc (x y z : PilotSeries) :
    evalOmega (ofPilotSeries ((x ++ y) ++ z)) =
      evalOmega (ofPilotSeries x) + evalOmega (ofPilotSeries y) + evalOmega (ofPilotSeries z) := by
  simpa [map_add, add_assoc] using congrArg evalOmega (ofPilotSeries_append_assoc x y z)

@[simp] theorem evalOmega_ofPilotSeries_add_nil (x : PilotSeries) :
    evalOmega (ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add x [])) =
      evalOmega (ofPilotSeries x) := by
  exact congrArg evalOmega (ofPilotSeries_add_nil x)

@[simp] theorem evalOmega_ofPilotSeries_nil_add (x : PilotSeries) :
    evalOmega (ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add [] x)) =
      evalOmega (ofPilotSeries x) := by
  exact congrArg evalOmega (ofPilotSeries_nil_add x)

theorem evalOmega_ofPilotSeries_add_assoc (x y z : PilotSeries) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.add x y) z)) =
      evalOmega (ofPilotSeries x) + evalOmega (ofPilotSeries y) + evalOmega (ofPilotSeries z) := by
  simpa [map_add, add_assoc] using congrArg evalOmega (ofPilotSeries_add_assoc x y z)

theorem evalOmega_ofPilotSeries_add_comm (x y : PilotSeries) :
    evalOmega (ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add x y)) =
      evalOmega (ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add y x)) := by
  exact congrArg evalOmega (ofPilotSeries_add_comm x y)

theorem evalOmega_ofPilotSeries_normalize (s : PilotSeries) :
    evalOmega (ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.normalize s)) =
      evalOmega (ofPilotSeries s) := by
  simpa [ofPilotSeries] using
    (evalOmega_ofPilotSeriesWith_normalize surrealSemanticsDefault s)

theorem ofPilotSeries_normalize (s : PilotSeries) :
    ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.normalize s) = ofPilotSeries s := by
  have hReal :
      HyperserialDescription.realize (K := Surreal)
          (ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.normalize s)) =
        HyperserialDescription.realize (K := Surreal) (ofPilotSeries s) := by
    change
      evalOmega (ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.normalize s)) =
        evalOmega (ofPilotSeries s)
    exact evalOmega_ofPilotSeries_normalize s
  exact HyperserialDescription.ext (K := Surreal) hReal

theorem ofPilotSeries_mul_monomial
    (c₁ c₂ : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₁ e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₂ e₂)) =
      ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.monomial (c₁ * c₂) (e₁ + e₂)) := by
  have hReal :
      HyperserialDescription.realize (K := Surreal)
          (ofPilotSeries
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₁ e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₂ e₂))) =
        HyperserialDescription.realize (K := Surreal)
          (ofPilotSeries
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial (c₁ * c₂) (e₁ + e₂))) := by
    change
      evalOmega
          (ofPilotSeries
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₁ e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₂ e₂))) =
        evalOmega
          (ofPilotSeries
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial (c₁ * c₂) (e₁ + e₂)))
    change
      evalOmega
          (ofPilotSeriesWith surrealSemanticsDefault
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₁ e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₂ e₂))) =
        evalOmega
          (ofPilotSeriesWith surrealSemanticsDefault
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial (c₁ * c₂) (e₁ + e₂)))
    exact evalOmega_ofPilotSeriesWith_mul_monomial surrealSemanticsDefault c₁ c₂ e₁ e₂
  exact HyperserialDescription.ext (K := Surreal) hReal

theorem evalOmega_ofPilotSeries_mul_monomial
    (c₁ c₂ : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₁ e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₂ e₂))) =
      evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial (c₁ * c₂) (e₁ + e₂))) := by
  exact congrArg evalOmega (ofPilotSeries_mul_monomial c₁ c₂ e₁ e₂)

@[simp] theorem evalOmega_ofPilotSeries_monomial_zero
    (e : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    evalOmega (ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e)) = 0 := by
  simpa [ofPilotSeries] using
    (evalOmega_ofPilotSeriesWith_monomial_zero surrealSemanticsDefault e)

@[simp] theorem evalOmega_ofPilotSeries_mul_monomial_zero_left
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) = 0 := by
  rw [evalOmega_ofPilotSeries_mul_monomial 0 c e₁ e₂]
  simp [zero_mul]

@[simp] theorem evalOmega_ofPilotSeries_mul_monomial_zero_right
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) = 0 := by
  rw [evalOmega_ofPilotSeries_mul_monomial c 0 e₁ e₂]
  simp [mul_zero]

theorem evalOmega_ofPilotSeries_mul_monomial_eq_zero_iff
    (c₁ c₂ : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₁ e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₂ e₂))) = 0 ↔
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial (c₁ * c₂) (e₁ + e₂))) = 0 := by
  constructor
  · intro h
    rwa [evalOmega_ofPilotSeries_mul_monomial c₁ c₂ e₁ e₂] at h
  · intro h
    rwa [evalOmega_ofPilotSeries_mul_monomial c₁ c₂ e₁ e₂]

theorem evalOmega_ofPilotSeries_mul_monomial_eq_zero_of_coeff_mul_eq_zero
    (c₁ c₂ : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (h : c₁ * c₂ = 0) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₁ e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₂ e₂))) = 0 := by
  rw [evalOmega_ofPilotSeries_mul_monomial c₁ c₂ e₁ e₂, h]
  exact evalOmega_ofPilotSeries_monomial_zero (e₁ + e₂)

theorem ofPilotSeries_eq_iff_evalOmega_eq (x y : PilotSeries) :
    ofPilotSeries x = ofPilotSeries y ↔
      evalOmega (ofPilotSeries x) = evalOmega (ofPilotSeries y) := by
  constructor
  · intro hxy
    exact congrArg evalOmega hxy
  · intro hxy
    have hReal :
        HyperserialDescription.realize (K := Surreal) (ofPilotSeries x) =
          HyperserialDescription.realize (K := Surreal) (ofPilotSeries y) := by
      simpa [evalOmega, evalRingHom_apply] using hxy
    exact HyperserialDescription.ext (K := Surreal) hReal

theorem ofPilotSeries_eq_zero_iff_evalOmega_eq_zero (s : PilotSeries) :
    ofPilotSeries s = 0 ↔ evalOmega (ofPilotSeries s) = 0 := by
  simpa [ofPilotSeries_nil] using (ofPilotSeries_eq_iff_evalOmega_eq s [])

theorem evalOmega_eq_zero_of_ofPilotSeries_eq_zero {s : PilotSeries}
    (h : ofPilotSeries s = 0) : evalOmega (ofPilotSeries s) = 0 := by
  simp [h]

theorem ofPilotSeries_eq_zero_of_evalOmega_eq_zero {s : PilotSeries}
    (h : evalOmega (ofPilotSeries s) = 0) : ofPilotSeries s = 0 := by
  exact (ofPilotSeries_eq_zero_iff_evalOmega_eq_zero s).2 h

@[simp] theorem ofPilotSeries_monomial_zero
    (e : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e) = 0 := by
  exact (ofPilotSeries_eq_zero_iff_evalOmega_eq_zero _).2
    (evalOmega_ofPilotSeries_monomial_zero e)

@[simp] theorem ofPilotSeries_mul_monomial_zero_left
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂)) = 0 := by
  rw [ofPilotSeries_mul_monomial 0 c e₁ e₂]
  simp [zero_mul]

@[simp] theorem ofPilotSeries_mul_monomial_zero_right
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂)) = 0 := by
  rw [ofPilotSeries_mul_monomial c 0 e₁ e₂]
  simp [mul_zero]

theorem ofPilotSeries_mul_monomial_eq_zero_iff
    (c₁ c₂ : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₁ e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₂ e₂)) = 0 ↔
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.monomial (c₁ * c₂) (e₁ + e₂)) = 0 := by
  constructor
  · intro h
    rwa [ofPilotSeries_mul_monomial c₁ c₂ e₁ e₂] at h
  · intro h
    rwa [ofPilotSeries_mul_monomial c₁ c₂ e₁ e₂]

theorem ofPilotSeries_mul_monomial_eq_zero_of_coeff_mul_eq_zero
    (c₁ c₂ : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (h : c₁ * c₂ = 0) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₁ e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₂ e₂)) = 0 := by
  rw [ofPilotSeries_mul_monomial c₁ c₂ e₁ e₂, h]
  exact ofPilotSeries_monomial_zero (e₁ + e₂)

theorem ofPilotSeries_add_mul_monomial_zero_left_lhs
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) = ofPilotSeries s := by
  rw [ofPilotSeries_add]
  simp

theorem ofPilotSeries_add_mul_monomial_zero_right_lhs
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) = ofPilotSeries s := by
  rw [ofPilotSeries_add]
  simp

theorem ofPilotSeries_add_mul_monomial_zero_left_rhs
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) = ofPilotSeries s := by
  rw [ofPilotSeries_add]
  simp

theorem ofPilotSeries_add_mul_monomial_zero_right_rhs
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) = ofPilotSeries s := by
  rw [ofPilotSeries_add]
  simp

theorem ofPilotSeries_add_mul_monomial_zero_left_lhs_eq_zero_iff
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) = 0 ↔
      ofPilotSeries s = 0 := by
  constructor
  · intro h
    rw [ofPilotSeries_add_mul_monomial_zero_left_lhs c e₁ e₂ s] at h
    exact h
  · intro h
    rw [ofPilotSeries_add_mul_monomial_zero_left_lhs c e₁ e₂ s]
    exact h

theorem ofPilotSeries_add_mul_monomial_zero_right_lhs_eq_zero_iff
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) = 0 ↔
      ofPilotSeries s = 0 := by
  constructor
  · intro h
    rw [ofPilotSeries_add_mul_monomial_zero_right_lhs c e₁ e₂ s] at h
    exact h
  · intro h
    rw [ofPilotSeries_add_mul_monomial_zero_right_lhs c e₁ e₂ s]
    exact h

theorem ofPilotSeries_add_mul_monomial_zero_left_rhs_eq_zero_iff
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) = 0 ↔
      ofPilotSeries s = 0 := by
  constructor
  · intro h
    rw [ofPilotSeries_add_mul_monomial_zero_left_rhs s c e₁ e₂] at h
    exact h
  · intro h
    rw [ofPilotSeries_add_mul_monomial_zero_left_rhs s c e₁ e₂]
    exact h

theorem ofPilotSeries_add_mul_monomial_zero_right_rhs_eq_zero_iff
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) = 0 ↔
      ofPilotSeries s = 0 := by
  constructor
  · intro h
    rw [ofPilotSeries_add_mul_monomial_zero_right_rhs s c e₁ e₂] at h
    exact h
  · intro h
    rw [ofPilotSeries_add_mul_monomial_zero_right_rhs s c e₁ e₂]
    exact h

theorem ofPilotSeries_add_mul_monomial_zero_left_lhs_eq_iff
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) =
      ofPilotSeries t ↔
      ofPilotSeries s = ofPilotSeries t := by
  constructor
  · intro h
    rw [ofPilotSeries_add_mul_monomial_zero_left_lhs c e₁ e₂ s] at h
    exact h
  · intro h
    rw [ofPilotSeries_add_mul_monomial_zero_left_lhs c e₁ e₂ s]
    exact h

theorem ofPilotSeries_add_mul_monomial_zero_right_lhs_eq_iff
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) =
      ofPilotSeries t ↔
      ofPilotSeries s = ofPilotSeries t := by
  constructor
  · intro h
    rw [ofPilotSeries_add_mul_monomial_zero_right_lhs c e₁ e₂ s] at h
    exact h
  · intro h
    rw [ofPilotSeries_add_mul_monomial_zero_right_lhs c e₁ e₂ s]
    exact h

theorem ofPilotSeries_add_mul_monomial_zero_left_rhs_eq_iff
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) =
      ofPilotSeries t ↔
      ofPilotSeries s = ofPilotSeries t := by
  constructor
  · intro h
    rw [ofPilotSeries_add_mul_monomial_zero_left_rhs s c e₁ e₂] at h
    exact h
  · intro h
    rw [ofPilotSeries_add_mul_monomial_zero_left_rhs s c e₁ e₂]
    exact h

theorem ofPilotSeries_add_mul_monomial_zero_right_rhs_eq_iff
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) =
      ofPilotSeries t ↔
      ofPilotSeries s = ofPilotSeries t := by
  constructor
  · intro h
    rw [ofPilotSeries_add_mul_monomial_zero_right_rhs s c e₁ e₂] at h
    exact h
  · intro h
    rw [ofPilotSeries_add_mul_monomial_zero_right_rhs s c e₁ e₂]
    exact h

theorem ofPilotSeries_add_mul_monomial_zero_left_lhs_eq_iff_right
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) =
      ofPilotSeries t ↔
      ofPilotSeries t = ofPilotSeries s := by
  simpa [eq_comm] using (ofPilotSeries_add_mul_monomial_zero_left_lhs_eq_iff c e₁ e₂ s t)

theorem ofPilotSeries_add_mul_monomial_zero_right_lhs_eq_iff_right
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) =
      ofPilotSeries t ↔
      ofPilotSeries t = ofPilotSeries s := by
  simpa [eq_comm] using (ofPilotSeries_add_mul_monomial_zero_right_lhs_eq_iff c e₁ e₂ s t)

theorem ofPilotSeries_add_mul_monomial_zero_left_rhs_eq_iff_right
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) =
      ofPilotSeries t ↔
      ofPilotSeries t = ofPilotSeries s := by
  simpa [eq_comm] using (ofPilotSeries_add_mul_monomial_zero_left_rhs_eq_iff s t c e₁ e₂)

theorem ofPilotSeries_add_mul_monomial_zero_right_rhs_eq_iff_right
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) =
      ofPilotSeries t ↔
      ofPilotSeries t = ofPilotSeries s := by
  simpa [eq_comm] using (ofPilotSeries_add_mul_monomial_zero_right_rhs_eq_iff s t c e₁ e₂)

theorem ofPilotSeries_add_mul_monomial_zero_left_lhs_eq_iff_left
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    ofPilotSeries t =
      ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) ↔
      ofPilotSeries t = ofPilotSeries s := by
  simpa [eq_comm] using (ofPilotSeries_add_mul_monomial_zero_left_lhs_eq_iff c e₁ e₂ s t)

theorem ofPilotSeries_add_mul_monomial_zero_right_lhs_eq_iff_left
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    ofPilotSeries t =
      ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) ↔
      ofPilotSeries t = ofPilotSeries s := by
  simpa [eq_comm] using (ofPilotSeries_add_mul_monomial_zero_right_lhs_eq_iff c e₁ e₂ s t)

theorem ofPilotSeries_add_mul_monomial_zero_left_rhs_eq_iff_left
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    ofPilotSeries t =
      ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) ↔
      ofPilotSeries t = ofPilotSeries s := by
  simpa [eq_comm] using (ofPilotSeries_add_mul_monomial_zero_left_rhs_eq_iff s t c e₁ e₂)

theorem ofPilotSeries_add_mul_monomial_zero_right_rhs_eq_iff_left
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    ofPilotSeries t =
      ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) ↔
      ofPilotSeries t = ofPilotSeries s := by
  simpa [eq_comm] using (ofPilotSeries_add_mul_monomial_zero_right_rhs_eq_iff s t c e₁ e₂)

theorem evalOmega_ofPilotSeries_add_mul_monomial_zero_left_lhs
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
            s)) = evalOmega (ofPilotSeries s) := by
  exact congrArg evalOmega (ofPilotSeries_add_mul_monomial_zero_left_lhs c e₁ e₂ s)

theorem evalOmega_ofPilotSeries_add_mul_monomial_zero_right_lhs
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
            s)) = evalOmega (ofPilotSeries s) := by
  exact congrArg evalOmega (ofPilotSeries_add_mul_monomial_zero_right_lhs c e₁ e₂ s)

theorem evalOmega_ofPilotSeries_add_mul_monomial_zero_left_rhs
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            s
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂)))) =
      evalOmega (ofPilotSeries s) := by
  exact congrArg evalOmega (ofPilotSeries_add_mul_monomial_zero_left_rhs s c e₁ e₂)

theorem evalOmega_ofPilotSeries_add_mul_monomial_zero_right_rhs
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            s
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂)))) =
      evalOmega (ofPilotSeries s) := by
  exact congrArg evalOmega (ofPilotSeries_add_mul_monomial_zero_right_rhs s c e₁ e₂)

theorem evalOmega_ofPilotSeries_add_mul_monomial_zero_left_lhs_eq_zero_iff
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
            s)) = 0 ↔
      evalOmega (ofPilotSeries s) = 0 := by
  constructor
  · intro h
    rw [evalOmega_ofPilotSeries_add_mul_monomial_zero_left_lhs c e₁ e₂ s] at h
    exact h
  · intro h
    rw [evalOmega_ofPilotSeries_add_mul_monomial_zero_left_lhs c e₁ e₂ s]
    exact h

theorem evalOmega_ofPilotSeries_add_mul_monomial_zero_right_lhs_eq_zero_iff
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
            s)) = 0 ↔
      evalOmega (ofPilotSeries s) = 0 := by
  constructor
  · intro h
    rw [evalOmega_ofPilotSeries_add_mul_monomial_zero_right_lhs c e₁ e₂ s] at h
    exact h
  · intro h
    rw [evalOmega_ofPilotSeries_add_mul_monomial_zero_right_lhs c e₁ e₂ s]
    exact h

theorem evalOmega_ofPilotSeries_add_mul_monomial_zero_left_rhs_eq_zero_iff
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            s
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂)))) = 0 ↔
      evalOmega (ofPilotSeries s) = 0 := by
  constructor
  · intro h
    rw [evalOmega_ofPilotSeries_add_mul_monomial_zero_left_rhs s c e₁ e₂] at h
    exact h
  · intro h
    rw [evalOmega_ofPilotSeries_add_mul_monomial_zero_left_rhs s c e₁ e₂]
    exact h

theorem evalOmega_ofPilotSeries_add_mul_monomial_zero_right_rhs_eq_zero_iff
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            s
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂)))) = 0 ↔
      evalOmega (ofPilotSeries s) = 0 := by
  constructor
  · intro h
    rw [evalOmega_ofPilotSeries_add_mul_monomial_zero_right_rhs s c e₁ e₂] at h
    exact h
  · intro h
    rw [evalOmega_ofPilotSeries_add_mul_monomial_zero_right_rhs s c e₁ e₂]
    exact h

theorem evalOmega_ofPilotSeries_add_mul_monomial_zero_left_lhs_eq_iff
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
            s)) =
      evalOmega (ofPilotSeries t) ↔
      evalOmega (ofPilotSeries s) = evalOmega (ofPilotSeries t) := by
  constructor
  · intro h
    rw [evalOmega_ofPilotSeries_add_mul_monomial_zero_left_lhs c e₁ e₂ s] at h
    exact h
  · intro h
    rw [evalOmega_ofPilotSeries_add_mul_monomial_zero_left_lhs c e₁ e₂ s]
    exact h

theorem evalOmega_ofPilotSeries_add_mul_monomial_zero_right_lhs_eq_iff
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
            s)) =
      evalOmega (ofPilotSeries t) ↔
      evalOmega (ofPilotSeries s) = evalOmega (ofPilotSeries t) := by
  constructor
  · intro h
    rw [evalOmega_ofPilotSeries_add_mul_monomial_zero_right_lhs c e₁ e₂ s] at h
    exact h
  · intro h
    rw [evalOmega_ofPilotSeries_add_mul_monomial_zero_right_lhs c e₁ e₂ s]
    exact h

theorem evalOmega_ofPilotSeries_add_mul_monomial_zero_left_rhs_eq_iff
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            s
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂)))) =
      evalOmega (ofPilotSeries t) ↔
      evalOmega (ofPilotSeries s) = evalOmega (ofPilotSeries t) := by
  constructor
  · intro h
    rw [evalOmega_ofPilotSeries_add_mul_monomial_zero_left_rhs s c e₁ e₂] at h
    exact h
  · intro h
    rw [evalOmega_ofPilotSeries_add_mul_monomial_zero_left_rhs s c e₁ e₂]
    exact h

theorem evalOmega_ofPilotSeries_add_mul_monomial_zero_right_rhs_eq_iff
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            s
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂)))) =
      evalOmega (ofPilotSeries t) ↔
      evalOmega (ofPilotSeries s) = evalOmega (ofPilotSeries t) := by
  constructor
  · intro h
    rw [evalOmega_ofPilotSeries_add_mul_monomial_zero_right_rhs s c e₁ e₂] at h
    exact h
  · intro h
    rw [evalOmega_ofPilotSeries_add_mul_monomial_zero_right_rhs s c e₁ e₂]
    exact h

theorem evalOmega_ofPilotSeries_add_mul_monomial_zero_left_lhs_eq_iff_right
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
            s)) =
      evalOmega (ofPilotSeries t) ↔
      evalOmega (ofPilotSeries t) = evalOmega (ofPilotSeries s) := by
  simpa [eq_comm] using (evalOmega_ofPilotSeries_add_mul_monomial_zero_left_lhs_eq_iff c e₁ e₂ s t)

theorem evalOmega_ofPilotSeries_add_mul_monomial_zero_right_lhs_eq_iff_right
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
            s)) =
      evalOmega (ofPilotSeries t) ↔
      evalOmega (ofPilotSeries t) = evalOmega (ofPilotSeries s) := by
  simpa [eq_comm] using (evalOmega_ofPilotSeries_add_mul_monomial_zero_right_lhs_eq_iff c e₁ e₂ s t)

theorem evalOmega_ofPilotSeries_add_mul_monomial_zero_left_rhs_eq_iff_right
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            s
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂)))) =
      evalOmega (ofPilotSeries t) ↔
      evalOmega (ofPilotSeries t) = evalOmega (ofPilotSeries s) := by
  simpa [eq_comm] using (evalOmega_ofPilotSeries_add_mul_monomial_zero_left_rhs_eq_iff s t c e₁ e₂)

theorem evalOmega_ofPilotSeries_add_mul_monomial_zero_right_rhs_eq_iff_right
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            s
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂)))) =
      evalOmega (ofPilotSeries t) ↔
      evalOmega (ofPilotSeries t) = evalOmega (ofPilotSeries s) := by
  simpa [eq_comm] using (evalOmega_ofPilotSeries_add_mul_monomial_zero_right_rhs_eq_iff s t c e₁ e₂)

theorem evalOmega_ofPilotSeries_add_mul_monomial_zero_left_lhs_eq_iff_left
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    evalOmega (ofPilotSeries t) =
      evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
            s)) ↔
      evalOmega (ofPilotSeries t) = evalOmega (ofPilotSeries s) := by
  simpa [eq_comm] using (evalOmega_ofPilotSeries_add_mul_monomial_zero_left_lhs_eq_iff c e₁ e₂ s t)

theorem evalOmega_ofPilotSeries_add_mul_monomial_zero_right_lhs_eq_iff_left
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    evalOmega (ofPilotSeries t) =
      evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
            s)) ↔
      evalOmega (ofPilotSeries t) = evalOmega (ofPilotSeries s) := by
  simpa [eq_comm] using (evalOmega_ofPilotSeries_add_mul_monomial_zero_right_lhs_eq_iff c e₁ e₂ s t)

theorem evalOmega_ofPilotSeries_add_mul_monomial_zero_left_rhs_eq_iff_left
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    evalOmega (ofPilotSeries t) =
      evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            s
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂)))) ↔
      evalOmega (ofPilotSeries t) = evalOmega (ofPilotSeries s) := by
  simpa [eq_comm] using (evalOmega_ofPilotSeries_add_mul_monomial_zero_left_rhs_eq_iff s t c e₁ e₂)

theorem evalOmega_ofPilotSeries_add_mul_monomial_zero_right_rhs_eq_iff_left
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    evalOmega (ofPilotSeries t) =
      evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            s
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂)))) ↔
      evalOmega (ofPilotSeries t) = evalOmega (ofPilotSeries s) := by
  simpa [eq_comm] using (evalOmega_ofPilotSeries_add_mul_monomial_zero_right_rhs_eq_iff s t c e₁ e₂)

theorem ofPilotSeries_add_mul_monomial_zero_left_lhs_cancel
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) =
      ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          t) ↔
      ofPilotSeries s = ofPilotSeries t := by
  constructor
  · intro h
    rw [ofPilotSeries_add_mul_monomial_zero_left_lhs c e₁ e₂ s,
      ofPilotSeries_add_mul_monomial_zero_left_lhs c e₁ e₂ t] at h
    exact h
  · intro h
    rw [ofPilotSeries_add_mul_monomial_zero_left_lhs c e₁ e₂ s,
      ofPilotSeries_add_mul_monomial_zero_left_lhs c e₁ e₂ t]
    exact h

theorem ofPilotSeries_add_mul_monomial_zero_right_lhs_cancel
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) =
      ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          t) ↔
      ofPilotSeries s = ofPilotSeries t := by
  constructor
  · intro h
    rw [ofPilotSeries_add_mul_monomial_zero_right_lhs c e₁ e₂ s,
      ofPilotSeries_add_mul_monomial_zero_right_lhs c e₁ e₂ t] at h
    exact h
  · intro h
    rw [ofPilotSeries_add_mul_monomial_zero_right_lhs c e₁ e₂ s,
      ofPilotSeries_add_mul_monomial_zero_right_lhs c e₁ e₂ t]
    exact h

theorem ofPilotSeries_add_mul_monomial_zero_left_rhs_cancel
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) =
      ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          t
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) ↔
      ofPilotSeries s = ofPilotSeries t := by
  constructor
  · intro h
    rw [ofPilotSeries_add_mul_monomial_zero_left_rhs s c e₁ e₂,
      ofPilotSeries_add_mul_monomial_zero_left_rhs t c e₁ e₂] at h
    exact h
  · intro h
    rw [ofPilotSeries_add_mul_monomial_zero_left_rhs s c e₁ e₂,
      ofPilotSeries_add_mul_monomial_zero_left_rhs t c e₁ e₂]
    exact h

theorem ofPilotSeries_add_mul_monomial_zero_right_rhs_cancel
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) =
      ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          t
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) ↔
      ofPilotSeries s = ofPilotSeries t := by
  constructor
  · intro h
    rw [ofPilotSeries_add_mul_monomial_zero_right_rhs s c e₁ e₂,
      ofPilotSeries_add_mul_monomial_zero_right_rhs t c e₁ e₂] at h
    exact h
  · intro h
    rw [ofPilotSeries_add_mul_monomial_zero_right_rhs s c e₁ e₂,
      ofPilotSeries_add_mul_monomial_zero_right_rhs t c e₁ e₂]
    exact h

theorem evalOmega_ofPilotSeries_add_mul_monomial_zero_left_lhs_cancel
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
            s)) =
      evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
            t)) ↔
      evalOmega (ofPilotSeries s) = evalOmega (ofPilotSeries t) := by
  constructor
  · intro h
    rw [evalOmega_ofPilotSeries_add_mul_monomial_zero_left_lhs c e₁ e₂ s,
      evalOmega_ofPilotSeries_add_mul_monomial_zero_left_lhs c e₁ e₂ t] at h
    exact h
  · intro h
    rw [evalOmega_ofPilotSeries_add_mul_monomial_zero_left_lhs c e₁ e₂ s,
      evalOmega_ofPilotSeries_add_mul_monomial_zero_left_lhs c e₁ e₂ t]
    exact h

theorem evalOmega_ofPilotSeries_add_mul_monomial_zero_right_lhs_cancel
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
            s)) =
      evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
            t)) ↔
      evalOmega (ofPilotSeries s) = evalOmega (ofPilotSeries t) := by
  constructor
  · intro h
    rw [evalOmega_ofPilotSeries_add_mul_monomial_zero_right_lhs c e₁ e₂ s,
      evalOmega_ofPilotSeries_add_mul_monomial_zero_right_lhs c e₁ e₂ t] at h
    exact h
  · intro h
    rw [evalOmega_ofPilotSeries_add_mul_monomial_zero_right_lhs c e₁ e₂ s,
      evalOmega_ofPilotSeries_add_mul_monomial_zero_right_lhs c e₁ e₂ t]
    exact h

theorem evalOmega_ofPilotSeries_add_mul_monomial_zero_left_rhs_cancel
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            s
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂)))) =
      evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            t
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂)))) ↔
      evalOmega (ofPilotSeries s) = evalOmega (ofPilotSeries t) := by
  constructor
  · intro h
    rw [evalOmega_ofPilotSeries_add_mul_monomial_zero_left_rhs s c e₁ e₂,
      evalOmega_ofPilotSeries_add_mul_monomial_zero_left_rhs t c e₁ e₂] at h
    exact h
  · intro h
    rw [evalOmega_ofPilotSeries_add_mul_monomial_zero_left_rhs s c e₁ e₂,
      evalOmega_ofPilotSeries_add_mul_monomial_zero_left_rhs t c e₁ e₂]
    exact h

theorem evalOmega_ofPilotSeries_add_mul_monomial_zero_right_rhs_cancel
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            s
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂)))) =
      evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            t
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂)))) ↔
      evalOmega (ofPilotSeries s) = evalOmega (ofPilotSeries t) := by
  constructor
  · intro h
    rw [evalOmega_ofPilotSeries_add_mul_monomial_zero_right_rhs s c e₁ e₂,
      evalOmega_ofPilotSeries_add_mul_monomial_zero_right_rhs t c e₁ e₂] at h
    exact h
  · intro h
    rw [evalOmega_ofPilotSeries_add_mul_monomial_zero_right_rhs s c e₁ e₂,
      evalOmega_ofPilotSeries_add_mul_monomial_zero_right_rhs t c e₁ e₂]
    exact h

theorem ofPilotSeries_add_cancel_left (x y z : PilotSeries) :
    ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add x y) =
      ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add x z) ↔
        ofPilotSeries y = ofPilotSeries z := by
  constructor
  · intro h
    have h' : ofPilotSeries x + ofPilotSeries y = ofPilotSeries x + ofPilotSeries z := by
      simpa [ofPilotSeries_add] using h
    exact add_left_cancel h'
  · intro h
    simp [ofPilotSeries_add, h]

theorem ofPilotSeries_add_cancel_right (x y z : PilotSeries) :
    ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add y x) =
      ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add z x) ↔
        ofPilotSeries y = ofPilotSeries z := by
  constructor
  · intro h
    have h' : ofPilotSeries y + ofPilotSeries x = ofPilotSeries z + ofPilotSeries x := by
      simpa [ofPilotSeries_add] using h
    exact add_right_cancel h'
  · intro h
    simp [ofPilotSeries_add, h]

theorem ofPilotSeries_add_eq_zero_iff (x y : PilotSeries) :
    ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add x y) = 0 ↔
      ofPilotSeries y = -(ofPilotSeries x) := by
  constructor
  · intro h
    have hxy : ofPilotSeries x + ofPilotSeries y = 0 := by
      simpa [ofPilotSeries_add] using h
    exact (eq_neg_iff_add_eq_zero).2 (by simpa [add_comm] using hxy)
  · intro h
    have hyx : ofPilotSeries y + ofPilotSeries x = 0 :=
      (eq_neg_iff_add_eq_zero).1 h
    have hxy : ofPilotSeries x + ofPilotSeries y = 0 := by
      simpa [add_comm] using hyx
    simpa [ofPilotSeries_add] using hxy

theorem ofPilotSeries_add_eq_zero_iff_left (x y : PilotSeries) :
    ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add x y) = 0 ↔
      ofPilotSeries x = -(ofPilotSeries y) := by
  constructor
  · intro h
    have hxy : ofPilotSeries x + ofPilotSeries y = 0 := by
      simpa [ofPilotSeries_add] using h
    exact (eq_neg_iff_add_eq_zero).2 hxy
  · intro h
    have hxy : ofPilotSeries x + ofPilotSeries y = 0 :=
      (eq_neg_iff_add_eq_zero).1 h
    simpa [ofPilotSeries_add] using hxy

theorem ofPilotSeries_add_normalize_left_eq_zero_iff (x y : PilotSeries) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) = 0 ↔
      ofPilotSeries y = -(ofPilotSeries x) := by
  simpa [ofPilotSeries_normalize] using
    (ofPilotSeries_add_eq_zero_iff (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y)

theorem ofPilotSeries_add_normalize_left_eq_zero_iff_left (x y : PilotSeries) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) = 0 ↔
      ofPilotSeries x = -(ofPilotSeries y) := by
  simpa [ofPilotSeries_normalize] using
    (ofPilotSeries_add_eq_zero_iff_left (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y)

theorem ofPilotSeries_add_normalize_right_eq_zero_iff (x y : PilotSeries) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      ofPilotSeries y = -(ofPilotSeries x) := by
  simpa [ofPilotSeries_normalize] using
    (ofPilotSeries_add_eq_zero_iff x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y))

theorem ofPilotSeries_add_normalize_right_eq_zero_iff_left (x y : PilotSeries) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      ofPilotSeries x = -(ofPilotSeries y) := by
  simpa [ofPilotSeries_normalize] using
    (ofPilotSeries_add_eq_zero_iff_left x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y))

theorem ofPilotSeries_add_normalize_eq_zero_iff (x y : PilotSeries) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      ofPilotSeries y = -(ofPilotSeries x) := by
  simpa [ofPilotSeries_normalize] using
    (ofPilotSeries_add_eq_zero_iff
      (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
      (HeytingLean.Numbers.Surreal.Hyperseries.normalize y))

theorem ofPilotSeries_add_normalize_eq_zero_iff_left (x y : PilotSeries) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      ofPilotSeries x = -(ofPilotSeries y) := by
  simpa [ofPilotSeries_normalize] using
    (ofPilotSeries_add_eq_zero_iff_left
      (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
      (HeytingLean.Numbers.Surreal.Hyperseries.normalize y))

theorem ofPilotSeries_add_normalize_left (x y : PilotSeries) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) =
      ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add x y) := by
  simp [ofPilotSeries_add, ofPilotSeries_normalize]

theorem ofPilotSeries_add_normalize_right (x y : PilotSeries) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) =
      ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add x y) := by
  simp [ofPilotSeries_add, ofPilotSeries_normalize]

theorem ofPilotSeries_add_normalize (x y : PilotSeries) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) =
      ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add x y) := by
  simp [ofPilotSeries_add, ofPilotSeries_normalize]

theorem ofPilotSeries_normalize_add (x y : PilotSeries) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.normalize
          (HeytingLean.Numbers.Surreal.Hyperseries.add x y)) =
      ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add x y) := by
  exact ofPilotSeries_normalize (HeytingLean.Numbers.Surreal.Hyperseries.add x y)

theorem ofPilotSeries_add_normalize_assoc (x y z : PilotSeries) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.normalize y) z)) =
      ofPilotSeries x + ofPilotSeries y + ofPilotSeries z := by
  simp [ofPilotSeries_add, ofPilotSeries_normalize, add_assoc]

theorem ofPilotSeries_add_normalize_cancel_left (x y z : PilotSeries) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) =
      ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) z) ↔
        ofPilotSeries y = ofPilotSeries z := by
  simpa using
    (ofPilotSeries_add_cancel_left (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y z)

theorem ofPilotSeries_add_normalize_cancel_right (x y z : PilotSeries) :
    ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          y (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)) =
      ofPilotSeries
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          z (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)) ↔
        ofPilotSeries y = ofPilotSeries z := by
  simpa using
    (ofPilotSeries_add_cancel_right (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y z)

theorem evalOmega_ofPilotSeries_add_cancel_left (x y z : PilotSeries) :
    evalOmega (ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add x y)) =
      evalOmega (ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add x z)) ↔
        evalOmega (ofPilotSeries y) = evalOmega (ofPilotSeries z) := by
  constructor
  · intro h
    have hOf :
        ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add x y) =
          ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add x z) :=
      (ofPilotSeries_eq_iff_evalOmega_eq _ _).2 h
    have hyz : ofPilotSeries y = ofPilotSeries z :=
      (ofPilotSeries_add_cancel_left x y z).1 hOf
    exact congrArg evalOmega hyz
  · intro h
    have hyz : ofPilotSeries y = ofPilotSeries z :=
      (ofPilotSeries_eq_iff_evalOmega_eq y z).2 h
    have hOf :
        ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add x y) =
          ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add x z) :=
      (ofPilotSeries_add_cancel_left x y z).2 hyz
    exact congrArg evalOmega hOf

theorem evalOmega_ofPilotSeries_add_cancel_right (x y z : PilotSeries) :
    evalOmega (ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add y x)) =
      evalOmega (ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add z x)) ↔
        evalOmega (ofPilotSeries y) = evalOmega (ofPilotSeries z) := by
  constructor
  · intro h
    have hOf :
        ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add y x) =
          ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add z x) :=
      (ofPilotSeries_eq_iff_evalOmega_eq _ _).2 h
    have hyz : ofPilotSeries y = ofPilotSeries z :=
      (ofPilotSeries_add_cancel_right x y z).1 hOf
    exact congrArg evalOmega hyz
  · intro h
    have hyz : ofPilotSeries y = ofPilotSeries z :=
      (ofPilotSeries_eq_iff_evalOmega_eq y z).2 h
    have hOf :
        ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add y x) =
          ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add z x) :=
      (ofPilotSeries_add_cancel_right x y z).2 hyz
    exact congrArg evalOmega hOf

theorem evalOmega_ofPilotSeries_add_eq_zero_iff (x y : PilotSeries) :
    evalOmega (ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add x y)) = 0 ↔
      evalOmega (ofPilotSeries y) = -(evalOmega (ofPilotSeries x)) := by
  have hadd :
      evalOmega (ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add x y)) =
        evalOmega (ofPilotSeries x) + evalOmega (ofPilotSeries y) := by
    simpa [HeytingLean.Numbers.Surreal.Hyperseries.add] using
      (evalOmega_ofPilotSeries_append x y)
  constructor
  · intro h
    have hxy : evalOmega (ofPilotSeries x) + evalOmega (ofPilotSeries y) = 0 := by
      simpa [hadd] using h
    have hyx : evalOmega (ofPilotSeries y) + evalOmega (ofPilotSeries x) = 0 := by
      simpa [add_comm] using hxy
    exact (eq_neg_iff_add_eq_zero).2 hyx
  · intro h
    have hyx : evalOmega (ofPilotSeries y) + evalOmega (ofPilotSeries x) = 0 :=
      (eq_neg_iff_add_eq_zero).1 h
    have hxy : evalOmega (ofPilotSeries x) + evalOmega (ofPilotSeries y) = 0 := by
      simpa [add_comm] using hyx
    exact hadd.trans hxy

theorem evalOmega_ofPilotSeries_add_eq_zero_iff_left (x y : PilotSeries) :
    evalOmega (ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add x y)) = 0 ↔
      evalOmega (ofPilotSeries x) = -(evalOmega (ofPilotSeries y)) := by
  constructor
  · intro h
    have hyx : evalOmega (ofPilotSeries y) = -(evalOmega (ofPilotSeries x)) :=
      (evalOmega_ofPilotSeries_add_eq_zero_iff x y).1 h
    have hyx' : evalOmega (ofPilotSeries y) + evalOmega (ofPilotSeries x) = 0 :=
      (eq_neg_iff_add_eq_zero).1 hyx
    have hxy : evalOmega (ofPilotSeries x) + evalOmega (ofPilotSeries y) = 0 := by
      simpa [add_comm] using hyx'
    exact (eq_neg_iff_add_eq_zero).2 hxy
  · intro h
    have hxy : evalOmega (ofPilotSeries x) + evalOmega (ofPilotSeries y) = 0 :=
      (eq_neg_iff_add_eq_zero).1 h
    have hyx : evalOmega (ofPilotSeries y) + evalOmega (ofPilotSeries x) = 0 := by
      simpa [add_comm] using hxy
    have hyx' : evalOmega (ofPilotSeries y) = -(evalOmega (ofPilotSeries x)) :=
      (eq_neg_iff_add_eq_zero).2 hyx
    exact (evalOmega_ofPilotSeries_add_eq_zero_iff x y).2 hyx'

theorem evalOmega_ofPilotSeries_add_normalize_left (x y : PilotSeries) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y)) =
      evalOmega (ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add x y)) := by
  exact congrArg evalOmega (ofPilotSeries_add_normalize_left x y)

theorem evalOmega_ofPilotSeries_add_normalize_right (x y : PilotSeries) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y))) =
      evalOmega (ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add x y)) := by
  exact congrArg evalOmega (ofPilotSeries_add_normalize_right x y)

theorem evalOmega_ofPilotSeries_add_normalize (x y : PilotSeries) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
            (HeytingLean.Numbers.Surreal.Hyperseries.normalize y))) =
      evalOmega (ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add x y)) := by
  exact congrArg evalOmega (ofPilotSeries_add_normalize x y)

theorem evalOmega_ofPilotSeries_normalize_add (x y : PilotSeries) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize
            (HeytingLean.Numbers.Surreal.Hyperseries.add x y))) =
      evalOmega (ofPilotSeries (HeytingLean.Numbers.Surreal.Hyperseries.add x y)) := by
  exact congrArg evalOmega (ofPilotSeries_normalize_add x y)

theorem evalOmega_ofPilotSeries_add_normalize_assoc (x y z : PilotSeries) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
            (HeytingLean.Numbers.Surreal.Hyperseries.add
              (HeytingLean.Numbers.Surreal.Hyperseries.normalize y) z))) =
      evalOmega (ofPilotSeries x) + evalOmega (ofPilotSeries y) + evalOmega (ofPilotSeries z) := by
  simpa [map_add, add_assoc] using congrArg evalOmega (ofPilotSeries_add_normalize_assoc x y z)

theorem evalOmega_ofPilotSeries_add_normalize_cancel_left (x y z : PilotSeries) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y)) =
      evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) z)) ↔
        evalOmega (ofPilotSeries y) = evalOmega (ofPilotSeries z) := by
  simpa using
    (evalOmega_ofPilotSeries_add_cancel_left
      (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y z)

theorem evalOmega_ofPilotSeries_add_normalize_cancel_right (x y z : PilotSeries) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            y (HeytingLean.Numbers.Surreal.Hyperseries.normalize x))) =
      evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            z (HeytingLean.Numbers.Surreal.Hyperseries.normalize x))) ↔
        evalOmega (ofPilotSeries y) = evalOmega (ofPilotSeries z) := by
  simpa using
    (evalOmega_ofPilotSeries_add_cancel_right
      (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y z)

theorem evalOmega_ofPilotSeries_add_normalize_left_eq_zero_iff (x y : PilotSeries) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y)) = 0 ↔
      evalOmega (ofPilotSeries y) = -(evalOmega (ofPilotSeries x)) := by
  simpa [ofPilotSeries_normalize] using
    (evalOmega_ofPilotSeries_add_eq_zero_iff
      (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y)

theorem evalOmega_ofPilotSeries_add_normalize_left_eq_zero_iff_left (x y : PilotSeries) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y)) = 0 ↔
      evalOmega (ofPilotSeries x) = -(evalOmega (ofPilotSeries y)) := by
  simpa [ofPilotSeries_normalize] using
    (evalOmega_ofPilotSeries_add_eq_zero_iff_left
      (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y)

theorem evalOmega_ofPilotSeries_add_normalize_right_eq_zero_iff (x y : PilotSeries) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y))) = 0 ↔
      evalOmega (ofPilotSeries y) = -(evalOmega (ofPilotSeries x)) := by
  simpa [ofPilotSeries_normalize] using
    (evalOmega_ofPilotSeries_add_eq_zero_iff
      x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y))

theorem evalOmega_ofPilotSeries_add_normalize_right_eq_zero_iff_left (x y : PilotSeries) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y))) = 0 ↔
      evalOmega (ofPilotSeries x) = -(evalOmega (ofPilotSeries y)) := by
  simpa [ofPilotSeries_normalize] using
    (evalOmega_ofPilotSeries_add_eq_zero_iff_left
      x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y))

theorem evalOmega_ofPilotSeries_add_normalize_eq_zero_iff (x y : PilotSeries) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
            (HeytingLean.Numbers.Surreal.Hyperseries.normalize y))) = 0 ↔
      evalOmega (ofPilotSeries y) = -(evalOmega (ofPilotSeries x)) := by
  simpa [ofPilotSeries_normalize] using
    (evalOmega_ofPilotSeries_add_eq_zero_iff
      (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
      (HeytingLean.Numbers.Surreal.Hyperseries.normalize y))

theorem evalOmega_ofPilotSeries_add_normalize_eq_zero_iff_left (x y : PilotSeries) :
    evalOmega
        (ofPilotSeries
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
            (HeytingLean.Numbers.Surreal.Hyperseries.normalize y))) = 0 ↔
      evalOmega (ofPilotSeries x) = -(evalOmega (ofPilotSeries y)) := by
  simpa [ofPilotSeries_normalize] using
    (evalOmega_ofPilotSeries_add_eq_zero_iff_left
      (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
      (HeytingLean.Numbers.Surreal.Hyperseries.normalize y))

theorem existsUnique_ofPilotSeries (s : PilotSeries) :
    ∃! h : HSNo, evalOmega h = evalOmega (ofPilotSeries s) := by
  exact existsUnique_hyperseries (evalOmega (ofPilotSeries s))

/-- Semantics-parametric surreal value induced by a pilot finite-support series. -/
noncomputable def pilotEvalWith (S : SurrealExpLogSemantics) (s : PilotSeries) : Surreal :=
  evalOmega (ofPilotSeriesWith S s)

/--
Bool-selector specialization of `pilotEvalWith`.
-/
noncomputable def pilotEvalSelect (useNontrivial : Bool) (s : PilotSeries) : Surreal :=
  pilotEvalWith (surrealSemantics useNontrivial) s

theorem pilotEvalSelect_false (s : PilotSeries) :
    pilotEvalSelect false s = evalOmega (ofPilotSeries s) := by
  rfl

@[simp] theorem pilotEvalSelect_append (useNontrivial : Bool) (x y : PilotSeries) :
    pilotEvalSelect useNontrivial (x ++ y) =
      pilotEvalSelect useNontrivial x + pilotEvalSelect useNontrivial y := by
  unfold pilotEvalSelect pilotEvalWith
  exact evalOmega_ofPilotSeriesWith_append (surrealSemantics useNontrivial) x y

@[simp] theorem pilotEvalSelect_add (useNontrivial : Bool) (x y : PilotSeries) :
    pilotEvalSelect useNontrivial (HeytingLean.Numbers.Surreal.Hyperseries.add x y) =
      pilotEvalSelect useNontrivial x + pilotEvalSelect useNontrivial y := by
  change pilotEvalSelect useNontrivial (x ++ y) =
    pilotEvalSelect useNontrivial x + pilotEvalSelect useNontrivial y
  exact pilotEvalSelect_append useNontrivial x y

@[simp] theorem pilotEvalSelect_normalize (useNontrivial : Bool) (s : PilotSeries) :
    pilotEvalSelect useNontrivial (HeytingLean.Numbers.Surreal.Hyperseries.normalize s) =
      pilotEvalSelect useNontrivial s := by
  unfold pilotEvalSelect pilotEvalWith
  exact evalOmega_ofPilotSeriesWith_normalize (surrealSemantics useNontrivial) s

theorem pilotEvalSelect_mul_monomial (useNontrivial : Bool)
    (c₁ c₂ : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₁ e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₂ e₂)) =
      pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.monomial (c₁ * c₂) (e₁ + e₂)) := by
  unfold pilotEvalSelect pilotEvalWith
  exact evalOmega_ofPilotSeriesWith_mul_monomial (surrealSemantics useNontrivial) c₁ c₂ e₁ e₂

theorem pilotEvalSelect_false_mul_monomial
    (c₁ c₂ : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₁ e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₂ e₂)) =
      pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.monomial (c₁ * c₂) (e₁ + e₂)) := by
  exact pilotEvalSelect_mul_monomial false c₁ c₂ e₁ e₂

@[simp] theorem pilotEvalSelect_monomial_zero
    (useNontrivial : Bool) (e : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect useNontrivial (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e) = 0 := by
  unfold pilotEvalSelect pilotEvalWith
  exact evalOmega_ofPilotSeriesWith_monomial_zero (surrealSemantics useNontrivial) e

@[simp] theorem pilotEvalSelect_nil (useNontrivial : Bool) :
    pilotEvalSelect useNontrivial ([] : PilotSeries) = 0 := by
  unfold pilotEvalSelect pilotEvalWith
  rw [evalOmega_ofPilotSeriesWith]
  simp

@[simp] theorem pilotEvalSelect_monomial (useNontrivial : Bool)
    (c : Int) (e : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect useNontrivial (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e) =
      HExpr.eval (surrealModelWith useNontrivial)
        (BridgePilot.ofSeries.{0} (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e)) := by
  unfold pilotEvalSelect pilotEvalWith
  simpa [surrealModelWith, surrealSemantics] using
    (evalOmega_ofPilotSeriesWith (surrealSemantics useNontrivial)
      (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e))

@[simp] theorem pilotEvalSelect_mul_monomial_zero_left
    (useNontrivial : Bool) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂)) = 0 := by
  rw [pilotEvalSelect_mul_monomial useNontrivial 0 c e₁ e₂]
  simp [zero_mul]

@[simp] theorem pilotEvalSelect_mul_monomial_zero_right
    (useNontrivial : Bool) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂)) = 0 := by
  rw [pilotEvalSelect_mul_monomial useNontrivial c 0 e₁ e₂]
  simp [mul_zero]

@[simp] theorem pilotEvalWith_nil (S : SurrealExpLogSemantics) :
    pilotEvalWith S ([] : PilotSeries) = 0 := by
  unfold pilotEvalWith
  rw [evalOmega_ofPilotSeriesWith]
  simp

@[simp] theorem pilotEvalWith_monomial (S : SurrealExpLogSemantics)
    (c : Int) (e : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalWith S (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e) =
      HExpr.eval (SurrealExpLogSemantics.toModel S)
        (BridgePilot.ofSeries.{0} (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e)) := by
  unfold pilotEvalWith
  exact evalOmega_ofPilotSeriesWith S (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e)

@[simp] theorem pilotEvalWith_append (S : SurrealExpLogSemantics) (x y : PilotSeries) :
    pilotEvalWith S (x ++ y) = pilotEvalWith S x + pilotEvalWith S y := by
  unfold pilotEvalWith
  exact evalOmega_ofPilotSeriesWith_append S x y

@[simp] theorem pilotEvalWith_add (S : SurrealExpLogSemantics) (x y : PilotSeries) :
    pilotEvalWith S (HeytingLean.Numbers.Surreal.Hyperseries.add x y) =
      pilotEvalWith S x + pilotEvalWith S y := by
  change pilotEvalWith S (x ++ y) = pilotEvalWith S x + pilotEvalWith S y
  exact pilotEvalWith_append S x y

@[simp] theorem pilotEvalWith_normalize (S : SurrealExpLogSemantics) (s : PilotSeries) :
    pilotEvalWith S (HeytingLean.Numbers.Surreal.Hyperseries.normalize s) = pilotEvalWith S s := by
  unfold pilotEvalWith
  exact evalOmega_ofPilotSeriesWith_normalize S s

theorem pilotEvalWith_mul_monomial
    (S : SurrealExpLogSemantics)
    (c₁ c₂ : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₁ e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₂ e₂)) =
      pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.monomial (c₁ * c₂) (e₁ + e₂)) := by
  unfold pilotEvalWith
  exact evalOmega_ofPilotSeriesWith_mul_monomial S c₁ c₂ e₁ e₂

@[simp] theorem pilotEvalWith_monomial_zero
    (S : SurrealExpLogSemantics) (e : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalWith S (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e) = 0 := by
  unfold pilotEvalWith
  exact evalOmega_ofPilotSeriesWith_monomial_zero S e

@[simp] theorem pilotEvalWith_mul_monomial_zero_left
    (S : SurrealExpLogSemantics) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂)) = 0 := by
  rw [pilotEvalWith_mul_monomial S 0 c e₁ e₂]
  simp [zero_mul]

@[simp] theorem pilotEvalWith_mul_monomial_zero_right
    (S : SurrealExpLogSemantics) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂)) = 0 := by
  rw [pilotEvalWith_mul_monomial S c 0 e₁ e₂]
  simp [mul_zero]

theorem pilotEvalWith_add_mul_monomial_zero_left_lhs
    (S : SurrealExpLogSemantics)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) = pilotEvalWith S s := by
  simp [pilotEvalWith_add]

theorem pilotEvalWith_add_mul_monomial_zero_right_lhs
    (S : SurrealExpLogSemantics)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) = pilotEvalWith S s := by
  simp [pilotEvalWith_add]

theorem pilotEvalWith_add_mul_monomial_zero_left_rhs
    (S : SurrealExpLogSemantics)
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) =
      pilotEvalWith S s := by
  simp [pilotEvalWith_add]

theorem pilotEvalWith_add_mul_monomial_zero_right_rhs
    (S : SurrealExpLogSemantics)
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) =
      pilotEvalWith S s := by
  simp [pilotEvalWith_add]

theorem pilotEvalWith_add_mul_monomial_zero_left_lhs_eq_zero_iff
    (S : SurrealExpLogSemantics)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) = 0 ↔
      pilotEvalWith S s = 0 := by
  constructor <;> intro h <;>
    simpa [pilotEvalWith_add_mul_monomial_zero_left_lhs] using h

theorem pilotEvalWith_add_mul_monomial_zero_right_lhs_eq_zero_iff
    (S : SurrealExpLogSemantics)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) = 0 ↔
      pilotEvalWith S s = 0 := by
  constructor <;> intro h <;>
    simpa [pilotEvalWith_add_mul_monomial_zero_right_lhs] using h

theorem pilotEvalWith_add_mul_monomial_zero_left_rhs_eq_zero_iff
    (S : SurrealExpLogSemantics)
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) = 0 ↔
      pilotEvalWith S s = 0 := by
  constructor <;> intro h <;>
    simpa [pilotEvalWith_add_mul_monomial_zero_left_rhs] using h

theorem pilotEvalWith_add_mul_monomial_zero_right_rhs_eq_zero_iff
    (S : SurrealExpLogSemantics)
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) = 0 ↔
      pilotEvalWith S s = 0 := by
  constructor <;> intro h <;>
    simpa [pilotEvalWith_add_mul_monomial_zero_right_rhs] using h

theorem pilotEvalWith_add_mul_monomial_zero_left_lhs_eq_iff
    (S : SurrealExpLogSemantics)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) =
      pilotEvalWith S t ↔
      pilotEvalWith S s = pilotEvalWith S t := by
  constructor <;> intro h <;>
    simpa [pilotEvalWith_add_mul_monomial_zero_left_lhs] using h

theorem pilotEvalWith_add_mul_monomial_zero_right_lhs_eq_iff
    (S : SurrealExpLogSemantics)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) =
      pilotEvalWith S t ↔
      pilotEvalWith S s = pilotEvalWith S t := by
  constructor <;> intro h <;>
    simpa [pilotEvalWith_add_mul_monomial_zero_right_lhs] using h

theorem pilotEvalWith_add_mul_monomial_zero_left_rhs_eq_iff
    (S : SurrealExpLogSemantics)
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) =
      pilotEvalWith S t ↔
      pilotEvalWith S s = pilotEvalWith S t := by
  constructor <;> intro h <;>
    simpa [pilotEvalWith_add_mul_monomial_zero_left_rhs] using h

theorem pilotEvalWith_add_mul_monomial_zero_right_rhs_eq_iff
    (S : SurrealExpLogSemantics)
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) =
      pilotEvalWith S t ↔
      pilotEvalWith S s = pilotEvalWith S t := by
  constructor <;> intro h <;>
    simpa [pilotEvalWith_add_mul_monomial_zero_right_rhs] using h

theorem pilotEvalWith_add_mul_monomial_zero_left_lhs_eq_zero_iff_left
    (S : SurrealExpLogSemantics)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    0 =
        pilotEvalWith S
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
            s) ↔
      0 = pilotEvalWith S s := by
  constructor
  · intro h
    exact Eq.symm <| (pilotEvalWith_add_mul_monomial_zero_left_lhs_eq_zero_iff S c e₁ e₂ s).1 (Eq.symm h)
  · intro h
    exact Eq.symm <| (pilotEvalWith_add_mul_monomial_zero_left_lhs_eq_zero_iff S c e₁ e₂ s).2 (Eq.symm h)

theorem pilotEvalWith_add_mul_monomial_zero_right_lhs_eq_zero_iff_left
    (S : SurrealExpLogSemantics)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    0 =
        pilotEvalWith S
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
            s) ↔
      0 = pilotEvalWith S s := by
  constructor
  · intro h
    exact Eq.symm <| (pilotEvalWith_add_mul_monomial_zero_right_lhs_eq_zero_iff S c e₁ e₂ s).1 (Eq.symm h)
  · intro h
    exact Eq.symm <| (pilotEvalWith_add_mul_monomial_zero_right_lhs_eq_zero_iff S c e₁ e₂ s).2 (Eq.symm h)

theorem pilotEvalWith_add_mul_monomial_zero_left_rhs_eq_zero_iff_left
    (S : SurrealExpLogSemantics)
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    0 =
        pilotEvalWith S
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            s
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) ↔
      0 = pilotEvalWith S s := by
  constructor
  · intro h
    exact Eq.symm <| (pilotEvalWith_add_mul_monomial_zero_left_rhs_eq_zero_iff S s c e₁ e₂).1 (Eq.symm h)
  · intro h
    exact Eq.symm <| (pilotEvalWith_add_mul_monomial_zero_left_rhs_eq_zero_iff S s c e₁ e₂).2 (Eq.symm h)

theorem pilotEvalWith_add_mul_monomial_zero_right_rhs_eq_zero_iff_left
    (S : SurrealExpLogSemantics)
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    0 =
        pilotEvalWith S
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            s
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) ↔
      0 = pilotEvalWith S s := by
  constructor
  · intro h
    exact Eq.symm <| (pilotEvalWith_add_mul_monomial_zero_right_rhs_eq_zero_iff S s c e₁ e₂).1 (Eq.symm h)
  · intro h
    exact Eq.symm <| (pilotEvalWith_add_mul_monomial_zero_right_rhs_eq_zero_iff S s c e₁ e₂).2 (Eq.symm h)

theorem pilotEvalWith_add_mul_monomial_zero_left_lhs_eq_zero_iff_right
    (S : SurrealExpLogSemantics)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) = 0 ↔
      0 = pilotEvalWith S s := by
  constructor
  · intro h
    exact Eq.symm ((pilotEvalWith_add_mul_monomial_zero_left_lhs_eq_zero_iff S c e₁ e₂ s).1 h)
  · intro h
    exact (pilotEvalWith_add_mul_monomial_zero_left_lhs_eq_zero_iff S c e₁ e₂ s).2 (Eq.symm h)

theorem pilotEvalWith_add_mul_monomial_zero_right_lhs_eq_zero_iff_right
    (S : SurrealExpLogSemantics)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) = 0 ↔
      0 = pilotEvalWith S s := by
  constructor
  · intro h
    exact Eq.symm ((pilotEvalWith_add_mul_monomial_zero_right_lhs_eq_zero_iff S c e₁ e₂ s).1 h)
  · intro h
    exact (pilotEvalWith_add_mul_monomial_zero_right_lhs_eq_zero_iff S c e₁ e₂ s).2 (Eq.symm h)

theorem pilotEvalWith_add_mul_monomial_zero_left_rhs_eq_zero_iff_right
    (S : SurrealExpLogSemantics)
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) = 0 ↔
      0 = pilotEvalWith S s := by
  constructor
  · intro h
    exact Eq.symm ((pilotEvalWith_add_mul_monomial_zero_left_rhs_eq_zero_iff S s c e₁ e₂).1 h)
  · intro h
    exact (pilotEvalWith_add_mul_monomial_zero_left_rhs_eq_zero_iff S s c e₁ e₂).2 (Eq.symm h)

theorem pilotEvalWith_add_mul_monomial_zero_right_rhs_eq_zero_iff_right
    (S : SurrealExpLogSemantics)
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) = 0 ↔
      0 = pilotEvalWith S s := by
  constructor
  · intro h
    exact Eq.symm ((pilotEvalWith_add_mul_monomial_zero_right_rhs_eq_zero_iff S s c e₁ e₂).1 h)
  · intro h
    exact (pilotEvalWith_add_mul_monomial_zero_right_rhs_eq_zero_iff S s c e₁ e₂).2 (Eq.symm h)

theorem pilotEvalWith_add_mul_monomial_zero_left_lhs_eq_iff_left
    (S : SurrealExpLogSemantics)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalWith S t =
      pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) ↔
      pilotEvalWith S t = pilotEvalWith S s := by
  constructor
  · intro h
    exact Eq.symm <| (pilotEvalWith_add_mul_monomial_zero_left_lhs_eq_iff S c e₁ e₂ s t).1 (Eq.symm h)
  · intro h
    exact Eq.symm <| (pilotEvalWith_add_mul_monomial_zero_left_lhs_eq_iff S c e₁ e₂ s t).2 (Eq.symm h)

theorem pilotEvalWith_add_mul_monomial_zero_right_lhs_eq_iff_left
    (S : SurrealExpLogSemantics)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalWith S t =
      pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) ↔
      pilotEvalWith S t = pilotEvalWith S s := by
  constructor
  · intro h
    exact Eq.symm <| (pilotEvalWith_add_mul_monomial_zero_right_lhs_eq_iff S c e₁ e₂ s t).1 (Eq.symm h)
  · intro h
    exact Eq.symm <| (pilotEvalWith_add_mul_monomial_zero_right_lhs_eq_iff S c e₁ e₂ s t).2 (Eq.symm h)

theorem pilotEvalWith_add_mul_monomial_zero_left_rhs_eq_iff_left
    (S : SurrealExpLogSemantics)
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalWith S t =
      pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) ↔
      pilotEvalWith S t = pilotEvalWith S s := by
  constructor
  · intro h
    exact Eq.symm <| (pilotEvalWith_add_mul_monomial_zero_left_rhs_eq_iff S s t c e₁ e₂).1 (Eq.symm h)
  · intro h
    exact Eq.symm <| (pilotEvalWith_add_mul_monomial_zero_left_rhs_eq_iff S s t c e₁ e₂).2 (Eq.symm h)

theorem pilotEvalWith_add_mul_monomial_zero_right_rhs_eq_iff_left
    (S : SurrealExpLogSemantics)
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalWith S t =
      pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) ↔
      pilotEvalWith S t = pilotEvalWith S s := by
  constructor
  · intro h
    exact Eq.symm <| (pilotEvalWith_add_mul_monomial_zero_right_rhs_eq_iff S s t c e₁ e₂).1 (Eq.symm h)
  · intro h
    exact Eq.symm <| (pilotEvalWith_add_mul_monomial_zero_right_rhs_eq_iff S s t c e₁ e₂).2 (Eq.symm h)

theorem pilotEvalWith_add_mul_monomial_zero_left_lhs_eq_iff_right
    (S : SurrealExpLogSemantics)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) =
      pilotEvalWith S t ↔
      pilotEvalWith S t = pilotEvalWith S s := by
  constructor
  · intro h
    exact Eq.symm ((pilotEvalWith_add_mul_monomial_zero_left_lhs_eq_iff S c e₁ e₂ s t).1 h)
  · intro h
    exact (pilotEvalWith_add_mul_monomial_zero_left_lhs_eq_iff S c e₁ e₂ s t).2 (Eq.symm h)

theorem pilotEvalWith_add_mul_monomial_zero_right_lhs_eq_iff_right
    (S : SurrealExpLogSemantics)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) =
      pilotEvalWith S t ↔
      pilotEvalWith S t = pilotEvalWith S s := by
  constructor
  · intro h
    exact Eq.symm ((pilotEvalWith_add_mul_monomial_zero_right_lhs_eq_iff S c e₁ e₂ s t).1 h)
  · intro h
    exact (pilotEvalWith_add_mul_monomial_zero_right_lhs_eq_iff S c e₁ e₂ s t).2 (Eq.symm h)

theorem pilotEvalWith_add_mul_monomial_zero_left_rhs_eq_iff_right
    (S : SurrealExpLogSemantics)
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) =
      pilotEvalWith S t ↔
      pilotEvalWith S t = pilotEvalWith S s := by
  constructor
  · intro h
    exact Eq.symm ((pilotEvalWith_add_mul_monomial_zero_left_rhs_eq_iff S s t c e₁ e₂).1 h)
  · intro h
    exact (pilotEvalWith_add_mul_monomial_zero_left_rhs_eq_iff S s t c e₁ e₂).2 (Eq.symm h)

theorem pilotEvalWith_add_mul_monomial_zero_right_rhs_eq_iff_right
    (S : SurrealExpLogSemantics)
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) =
      pilotEvalWith S t ↔
      pilotEvalWith S t = pilotEvalWith S s := by
  constructor
  · intro h
    exact Eq.symm ((pilotEvalWith_add_mul_monomial_zero_right_rhs_eq_iff S s t c e₁ e₂).1 h)
  · intro h
    exact (pilotEvalWith_add_mul_monomial_zero_right_rhs_eq_iff S s t c e₁ e₂).2 (Eq.symm h)

theorem pilotEvalWith_add_mul_monomial_zero_left_lhs_cancel
    (S : SurrealExpLogSemantics)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) =
      pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          t) ↔
      pilotEvalWith S s = pilotEvalWith S t := by
  constructor <;> intro h <;>
    simpa [pilotEvalWith_add_mul_monomial_zero_left_lhs] using h

theorem pilotEvalWith_add_mul_monomial_zero_right_lhs_cancel
    (S : SurrealExpLogSemantics)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) =
      pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          t) ↔
      pilotEvalWith S s = pilotEvalWith S t := by
  constructor <;> intro h <;>
    simpa [pilotEvalWith_add_mul_monomial_zero_right_lhs] using h

theorem pilotEvalWith_add_mul_monomial_zero_left_rhs_cancel
    (S : SurrealExpLogSemantics)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) =
      pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          t
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) ↔
      pilotEvalWith S s = pilotEvalWith S t := by
  constructor <;> intro h <;>
    simpa [pilotEvalWith_add_mul_monomial_zero_left_rhs] using h

theorem pilotEvalWith_add_mul_monomial_zero_right_rhs_cancel
    (S : SurrealExpLogSemantics)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) =
      pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          t
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) ↔
      pilotEvalWith S s = pilotEvalWith S t := by
  constructor <;> intro h <;>
    simpa [pilotEvalWith_add_mul_monomial_zero_right_rhs] using h

theorem pilotEvalWith_mul_monomial_eq_zero_iff
    (S : SurrealExpLogSemantics)
    (c₁ c₂ : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₁ e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₂ e₂)) = 0 ↔
      pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.monomial (c₁ * c₂) (e₁ + e₂)) = 0 := by
  constructor
  · intro h
    rwa [pilotEvalWith_mul_monomial S c₁ c₂ e₁ e₂] at h
  · intro h
    rwa [pilotEvalWith_mul_monomial S c₁ c₂ e₁ e₂]

theorem pilotEvalWith_mul_monomial_eq_zero_of_coeff_mul_eq_zero
    (S : SurrealExpLogSemantics)
    (c₁ c₂ : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (h : c₁ * c₂ = 0) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₁ e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₂ e₂)) = 0 := by
  rw [pilotEvalWith_mul_monomial S c₁ c₂ e₁ e₂, h]
  exact pilotEvalWith_monomial_zero S (e₁ + e₂)

theorem pilotEvalWith_append_assoc (S : SurrealExpLogSemantics) (x y z : PilotSeries) :
    pilotEvalWith S ((x ++ y) ++ z) = pilotEvalWith S x + pilotEvalWith S y + pilotEvalWith S z := by
  rw [pilotEvalWith_append, pilotEvalWith_append]

theorem pilotEvalWith_add_assoc (S : SurrealExpLogSemantics) (x y z : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.add x y) z) =
      pilotEvalWith S x + pilotEvalWith S y + pilotEvalWith S z := by
  simpa [HeytingLean.Numbers.Surreal.Hyperseries.add, List.append_assoc] using
    (pilotEvalWith_append_assoc S x y z)

theorem pilotEvalWith_add_comm (S : SurrealExpLogSemantics) (x y : PilotSeries) :
    pilotEvalWith S (HeytingLean.Numbers.Surreal.Hyperseries.add x y) =
      pilotEvalWith S (HeytingLean.Numbers.Surreal.Hyperseries.add y x) := by
  simpa [HeytingLean.Numbers.Surreal.Hyperseries.add] using
    (show pilotEvalWith S (x ++ y) = pilotEvalWith S (y ++ x) by
      rw [pilotEvalWith_append, pilotEvalWith_append]
      exact add_comm _ _)

/-- Surreal value induced by a pilot finite-support series through canonical description. -/
noncomputable def pilotEval (s : PilotSeries) : Surreal :=
  evalOmega (ofPilotSeries s)

@[simp] theorem pilotEval_eq_evalOmega_ofPilotSeries (s : PilotSeries) :
    pilotEval s = evalOmega (ofPilotSeries s) := rfl

theorem pilotEvalSelect_false_eq_pilotEval (s : PilotSeries) :
    pilotEvalSelect false s = pilotEval s := by
  rfl

@[simp] theorem pilotEval_nil :
    pilotEval ([] : PilotSeries) = 0 := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_nil surrealSemanticsDefault)

@[simp] theorem pilotEval_monomial (c : Int) (e : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEval (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e) =
      HExpr.eval surrealModel
        (BridgePilot.ofSeries.{0} (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e)) := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries, surrealModel, instHyperserialModelSurreal,
    surrealSemanticsDefault] using
    (pilotEvalWith_monomial surrealSemanticsDefault c e)

@[simp] theorem pilotEval_append (x y : PilotSeries) :
    pilotEval (x ++ y) = pilotEval x + pilotEval y := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_append surrealSemanticsDefault x y)

@[simp] theorem pilotEval_add (x y : PilotSeries) :
    pilotEval (HeytingLean.Numbers.Surreal.Hyperseries.add x y) = pilotEval x + pilotEval y := by
  simpa [HeytingLean.Numbers.Surreal.Hyperseries.add] using pilotEval_append x y

@[simp] theorem pilotEval_normalize (s : PilotSeries) :
    pilotEval (HeytingLean.Numbers.Surreal.Hyperseries.normalize s) = pilotEval s := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_normalize surrealSemanticsDefault s)

theorem pilotEval_mul_monomial
    (c₁ c₂ : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₁ e₁)
        (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₂ e₂)) =
      pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.monomial (c₁ * c₂) (e₁ + e₂)) := by
  unfold pilotEval
  exact pilotEvalWith_mul_monomial surrealSemanticsDefault c₁ c₂ e₁ e₂

@[simp] theorem pilotEval_monomial_zero
    (e : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEval (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e) = 0 := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_monomial_zero surrealSemanticsDefault e)

@[simp] theorem pilotEval_mul_monomial_zero_left
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂)) = 0 := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_mul_monomial_zero_left surrealSemanticsDefault c e₁ e₂)

@[simp] theorem pilotEval_mul_monomial_zero_right
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂)) = 0 := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_mul_monomial_zero_right surrealSemanticsDefault c e₁ e₂)

theorem pilotEval_mul_monomial_eq_zero_iff
    (c₁ c₂ : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₁ e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₂ e₂)) = 0 ↔
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.monomial (c₁ * c₂) (e₁ + e₂)) = 0 := by
  unfold pilotEval
  exact pilotEvalWith_mul_monomial_eq_zero_iff surrealSemanticsDefault c₁ c₂ e₁ e₂

theorem pilotEval_mul_monomial_eq_zero_of_coeff_mul_eq_zero
    (c₁ c₂ : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (h : c₁ * c₂ = 0) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₁ e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₂ e₂)) = 0 := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_mul_monomial_eq_zero_of_coeff_mul_eq_zero
      surrealSemanticsDefault c₁ c₂ e₁ e₂ h)

theorem pilotEval_add_mul_monomial_zero_left_lhs
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) = pilotEval s := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_mul_monomial_zero_left_lhs surrealSemanticsDefault c e₁ e₂ s)

theorem pilotEval_add_mul_monomial_zero_right_lhs
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) = pilotEval s := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_mul_monomial_zero_right_lhs surrealSemanticsDefault c e₁ e₂ s)

theorem pilotEval_add_mul_monomial_zero_left_rhs
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) =
      pilotEval s := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_mul_monomial_zero_left_rhs surrealSemanticsDefault s c e₁ e₂)

theorem pilotEval_add_mul_monomial_zero_right_rhs
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) =
      pilotEval s := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_mul_monomial_zero_right_rhs surrealSemanticsDefault s c e₁ e₂)

theorem pilotEval_add_mul_monomial_zero_left_lhs_eq_zero_iff
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) = 0 ↔
      pilotEval s = 0 := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_mul_monomial_zero_left_lhs_eq_zero_iff surrealSemanticsDefault c e₁ e₂ s)

theorem pilotEval_add_mul_monomial_zero_right_lhs_eq_zero_iff
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) = 0 ↔
      pilotEval s = 0 := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_mul_monomial_zero_right_lhs_eq_zero_iff surrealSemanticsDefault c e₁ e₂ s)

theorem pilotEval_add_mul_monomial_zero_left_rhs_eq_zero_iff
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) = 0 ↔
      pilotEval s = 0 := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_mul_monomial_zero_left_rhs_eq_zero_iff surrealSemanticsDefault s c e₁ e₂)

theorem pilotEval_add_mul_monomial_zero_right_rhs_eq_zero_iff
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) = 0 ↔
      pilotEval s = 0 := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_mul_monomial_zero_right_rhs_eq_zero_iff surrealSemanticsDefault s c e₁ e₂)

theorem pilotEval_add_mul_monomial_zero_left_lhs_eq_zero_iff_left
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    0 =
        pilotEval
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
            s) ↔
      0 = pilotEval s := by
  constructor
  · intro h
    exact Eq.symm <| (pilotEval_add_mul_monomial_zero_left_lhs_eq_zero_iff c e₁ e₂ s).1 (Eq.symm h)
  · intro h
    exact Eq.symm <| (pilotEval_add_mul_monomial_zero_left_lhs_eq_zero_iff c e₁ e₂ s).2 (Eq.symm h)

theorem pilotEval_add_mul_monomial_zero_right_lhs_eq_zero_iff_left
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    0 =
        pilotEval
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
            s) ↔
      0 = pilotEval s := by
  constructor
  · intro h
    exact Eq.symm <| (pilotEval_add_mul_monomial_zero_right_lhs_eq_zero_iff c e₁ e₂ s).1 (Eq.symm h)
  · intro h
    exact Eq.symm <| (pilotEval_add_mul_monomial_zero_right_lhs_eq_zero_iff c e₁ e₂ s).2 (Eq.symm h)

theorem pilotEval_add_mul_monomial_zero_left_rhs_eq_zero_iff_left
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    0 =
        pilotEval
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            s
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) ↔
      0 = pilotEval s := by
  constructor
  · intro h
    exact Eq.symm <| (pilotEval_add_mul_monomial_zero_left_rhs_eq_zero_iff s c e₁ e₂).1 (Eq.symm h)
  · intro h
    exact Eq.symm <| (pilotEval_add_mul_monomial_zero_left_rhs_eq_zero_iff s c e₁ e₂).2 (Eq.symm h)

theorem pilotEval_add_mul_monomial_zero_right_rhs_eq_zero_iff_left
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    0 =
        pilotEval
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            s
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) ↔
      0 = pilotEval s := by
  constructor
  · intro h
    exact Eq.symm <| (pilotEval_add_mul_monomial_zero_right_rhs_eq_zero_iff s c e₁ e₂).1 (Eq.symm h)
  · intro h
    exact Eq.symm <| (pilotEval_add_mul_monomial_zero_right_rhs_eq_zero_iff s c e₁ e₂).2 (Eq.symm h)

theorem pilotEval_add_mul_monomial_zero_left_lhs_eq_zero_iff_right
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) = 0 ↔
      0 = pilotEval s := by
  constructor
  · intro h
    exact Eq.symm ((pilotEval_add_mul_monomial_zero_left_lhs_eq_zero_iff c e₁ e₂ s).1 h)
  · intro h
    exact (pilotEval_add_mul_monomial_zero_left_lhs_eq_zero_iff c e₁ e₂ s).2 (Eq.symm h)

theorem pilotEval_add_mul_monomial_zero_right_lhs_eq_zero_iff_right
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) = 0 ↔
      0 = pilotEval s := by
  constructor
  · intro h
    exact Eq.symm ((pilotEval_add_mul_monomial_zero_right_lhs_eq_zero_iff c e₁ e₂ s).1 h)
  · intro h
    exact (pilotEval_add_mul_monomial_zero_right_lhs_eq_zero_iff c e₁ e₂ s).2 (Eq.symm h)

theorem pilotEval_add_mul_monomial_zero_left_rhs_eq_zero_iff_right
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) = 0 ↔
      0 = pilotEval s := by
  constructor
  · intro h
    exact Eq.symm ((pilotEval_add_mul_monomial_zero_left_rhs_eq_zero_iff s c e₁ e₂).1 h)
  · intro h
    exact (pilotEval_add_mul_monomial_zero_left_rhs_eq_zero_iff s c e₁ e₂).2 (Eq.symm h)

theorem pilotEval_add_mul_monomial_zero_right_rhs_eq_zero_iff_right
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) = 0 ↔
      0 = pilotEval s := by
  constructor
  · intro h
    exact Eq.symm ((pilotEval_add_mul_monomial_zero_right_rhs_eq_zero_iff s c e₁ e₂).1 h)
  · intro h
    exact (pilotEval_add_mul_monomial_zero_right_rhs_eq_zero_iff s c e₁ e₂).2 (Eq.symm h)

theorem pilotEval_add_mul_monomial_zero_left_lhs_eq_iff
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) =
      pilotEval t ↔
      pilotEval s = pilotEval t := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_mul_monomial_zero_left_lhs_eq_iff surrealSemanticsDefault c e₁ e₂ s t)

theorem pilotEval_add_mul_monomial_zero_right_lhs_eq_iff
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) =
      pilotEval t ↔
      pilotEval s = pilotEval t := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_mul_monomial_zero_right_lhs_eq_iff surrealSemanticsDefault c e₁ e₂ s t)

theorem pilotEval_add_mul_monomial_zero_left_rhs_eq_iff
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) =
      pilotEval t ↔
      pilotEval s = pilotEval t := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_mul_monomial_zero_left_rhs_eq_iff surrealSemanticsDefault s t c e₁ e₂)

theorem pilotEval_add_mul_monomial_zero_right_rhs_eq_iff
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) =
      pilotEval t ↔
      pilotEval s = pilotEval t := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_mul_monomial_zero_right_rhs_eq_iff surrealSemanticsDefault s t c e₁ e₂)

theorem pilotEval_add_mul_monomial_zero_left_lhs_eq_iff_right
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) =
      pilotEval t ↔
      pilotEval t = pilotEval s := by
  simpa [eq_comm] using (pilotEval_add_mul_monomial_zero_left_lhs_eq_iff c e₁ e₂ s t)

theorem pilotEval_add_mul_monomial_zero_right_lhs_eq_iff_right
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) =
      pilotEval t ↔
      pilotEval t = pilotEval s := by
  simpa [eq_comm] using (pilotEval_add_mul_monomial_zero_right_lhs_eq_iff c e₁ e₂ s t)

theorem pilotEval_add_mul_monomial_zero_left_rhs_eq_iff_right
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) =
      pilotEval t ↔
      pilotEval t = pilotEval s := by
  simpa [eq_comm] using (pilotEval_add_mul_monomial_zero_left_rhs_eq_iff s t c e₁ e₂)

theorem pilotEval_add_mul_monomial_zero_right_rhs_eq_iff_right
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) =
      pilotEval t ↔
      pilotEval t = pilotEval s := by
  simpa [eq_comm] using (pilotEval_add_mul_monomial_zero_right_rhs_eq_iff s t c e₁ e₂)

theorem pilotEval_add_mul_monomial_zero_left_lhs_eq_iff_left
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEval t =
      pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) ↔
      pilotEval t = pilotEval s := by
  simpa [eq_comm] using (pilotEval_add_mul_monomial_zero_left_lhs_eq_iff c e₁ e₂ s t)

theorem pilotEval_add_mul_monomial_zero_right_lhs_eq_iff_left
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEval t =
      pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) ↔
      pilotEval t = pilotEval s := by
  simpa [eq_comm] using (pilotEval_add_mul_monomial_zero_right_lhs_eq_iff c e₁ e₂ s t)

theorem pilotEval_add_mul_monomial_zero_left_rhs_eq_iff_left
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEval t =
      pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) ↔
      pilotEval t = pilotEval s := by
  simpa [eq_comm] using (pilotEval_add_mul_monomial_zero_left_rhs_eq_iff s t c e₁ e₂)

theorem pilotEval_add_mul_monomial_zero_right_rhs_eq_iff_left
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEval t =
      pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) ↔
      pilotEval t = pilotEval s := by
  simpa [eq_comm] using (pilotEval_add_mul_monomial_zero_right_rhs_eq_iff s t c e₁ e₂)

theorem pilotEval_add_mul_monomial_zero_left_lhs_cancel
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) =
      pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          t) ↔
      pilotEval s = pilotEval t := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_mul_monomial_zero_left_lhs_cancel surrealSemanticsDefault c e₁ e₂ s t)

theorem pilotEval_add_mul_monomial_zero_right_lhs_cancel
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) =
      pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          t) ↔
      pilotEval s = pilotEval t := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_mul_monomial_zero_right_lhs_cancel surrealSemanticsDefault c e₁ e₂ s t)

theorem pilotEval_add_mul_monomial_zero_left_rhs_cancel
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) =
      pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          t
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) ↔
      pilotEval s = pilotEval t := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_mul_monomial_zero_left_rhs_cancel surrealSemanticsDefault c e₁ e₂ s t)

theorem pilotEval_add_mul_monomial_zero_right_rhs_cancel
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) =
      pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          t
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) ↔
      pilotEval s = pilotEval t := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_mul_monomial_zero_right_rhs_cancel surrealSemanticsDefault c e₁ e₂ s t)

theorem pilotEvalWith_eq_iff_ofPilotSeriesWith_eq
    (S : SurrealExpLogSemantics) (x y : PilotSeries) :
    pilotEvalWith S x = pilotEvalWith S y ↔
      ofPilotSeriesWith S x = ofPilotSeriesWith S y := by
  constructor
  · intro hxy
    apply HyperserialDescription.ext (K := Surreal)
    simpa [pilotEvalWith, evalOmega, evalRingHom_apply] using hxy
  · intro hxy
    exact congrArg evalOmega hxy

theorem pilotEvalWith_eq_zero_iff_ofPilotSeriesWith_eq_zero
    (S : SurrealExpLogSemantics) (s : PilotSeries) :
    pilotEvalWith S s = 0 ↔ ofPilotSeriesWith S s = 0 := by
  constructor
  · intro hs
    apply HyperserialDescription.ext (K := Surreal)
    change evalOmega (ofPilotSeriesWith S s) = evalOmega (0 : HSNo)
    simpa [pilotEvalWith] using hs
  · intro hs
    have hEval : evalOmega (ofPilotSeriesWith S s) = evalOmega (0 : HSNo) :=
      congrArg evalOmega hs
    simpa [pilotEvalWith] using hEval

theorem pilotEvalSelect_eq_iff_ofPilotSeriesSelect_eq
    (useNontrivial : Bool) (x y : PilotSeries) :
    pilotEvalSelect useNontrivial x = pilotEvalSelect useNontrivial y ↔
      ofPilotSeriesSelect useNontrivial x = ofPilotSeriesSelect useNontrivial y := by
  simpa [pilotEvalSelect, ofPilotSeriesSelect] using
    (pilotEvalWith_eq_iff_ofPilotSeriesWith_eq (surrealSemantics useNontrivial) x y)

theorem pilotEvalSelect_false_eq_iff_ofPilotSeriesSelect_eq (x y : PilotSeries) :
    pilotEvalSelect false x = pilotEvalSelect false y ↔
      ofPilotSeriesSelect false x = ofPilotSeriesSelect false y := by
  simpa using (pilotEvalSelect_eq_iff_ofPilotSeriesSelect_eq false x y)

theorem pilotEvalSelect_eq_iff_ofPilotSeriesWith_eq
    (useNontrivial : Bool) (x y : PilotSeries) :
    pilotEvalSelect useNontrivial x = pilotEvalSelect useNontrivial y ↔
      ofPilotSeriesWith (surrealSemantics useNontrivial) x =
        ofPilotSeriesWith (surrealSemantics useNontrivial) y := by
  change
    pilotEvalWith (surrealSemantics useNontrivial) x =
      pilotEvalWith (surrealSemantics useNontrivial) y ↔
      ofPilotSeriesWith (surrealSemantics useNontrivial) x =
        ofPilotSeriesWith (surrealSemantics useNontrivial) y
  exact pilotEvalWith_eq_iff_ofPilotSeriesWith_eq (surrealSemantics useNontrivial) x y

theorem pilotEval_eq_iff_ofPilotSeries_eq (x y : PilotSeries) :
    pilotEval x = pilotEval y ↔ ofPilotSeries x = ofPilotSeries y := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_eq_iff_ofPilotSeriesWith_eq surrealSemanticsDefault x y)

theorem pilotEval_eq_iff_ofPilotSeriesWith_eq (x y : PilotSeries) :
    pilotEval x = pilotEval y ↔
      ofPilotSeriesWith surrealSemanticsDefault x =
        ofPilotSeriesWith surrealSemanticsDefault y := by
  simpa [ofPilotSeries] using (pilotEval_eq_iff_ofPilotSeries_eq x y)

theorem pilotEvalSelect_false_eq_iff_ofPilotSeries_eq (x y : PilotSeries) :
    pilotEvalSelect false x = pilotEvalSelect false y ↔ ofPilotSeries x = ofPilotSeries y := by
  simpa [pilotEvalSelect_false_eq_pilotEval] using (pilotEval_eq_iff_ofPilotSeries_eq x y)

theorem pilotEvalSelect_false_eq_iff_ofPilotSeriesWith_eq (x y : PilotSeries) :
    pilotEvalSelect false x = pilotEvalSelect false y ↔
      ofPilotSeriesWith surrealSemanticsDefault x =
        ofPilotSeriesWith surrealSemanticsDefault y := by
  simpa [pilotEvalSelect_false_eq_pilotEval] using (pilotEval_eq_iff_ofPilotSeriesWith_eq x y)

theorem pilotEvalSelect_eq_iff_ofPilotSeries_eq (x y : PilotSeries) :
    pilotEvalSelect false x = pilotEvalSelect false y ↔ ofPilotSeries x = ofPilotSeries y := by
  exact pilotEvalSelect_false_eq_iff_ofPilotSeries_eq x y

theorem pilotEval_eq_iff_ofPilotSeriesSelect_false_eq (x y : PilotSeries) :
    pilotEval x = pilotEval y ↔
      ofPilotSeriesSelect false x = ofPilotSeriesSelect false y := by
  simpa [pilotEvalSelect_false_eq_pilotEval] using
    (pilotEvalSelect_false_eq_iff_ofPilotSeriesSelect_eq x y)

theorem pilotEvalSelect_eq_zero_iff_ofPilotSeriesSelect_eq_zero
    (useNontrivial : Bool) (s : PilotSeries) :
    pilotEvalSelect useNontrivial s = 0 ↔
      ofPilotSeriesSelect useNontrivial s = 0 := by
  constructor
  · intro h
    apply HyperserialDescription.ext (K := Surreal)
    change evalOmega (ofPilotSeriesSelect useNontrivial s) = evalOmega (0 : HSNo)
    simpa [pilotEvalSelect] using h
  · intro h
    have hEval : evalOmega (ofPilotSeriesSelect useNontrivial s) = evalOmega (0 : HSNo) :=
      congrArg evalOmega h
    simpa [pilotEvalSelect] using hEval

theorem pilotEvalSelect_eq_zero_iff_ofPilotSeriesWith_eq_zero
    (useNontrivial : Bool) (s : PilotSeries) :
    pilotEvalSelect useNontrivial s = 0 ↔
      ofPilotSeriesWith (surrealSemantics useNontrivial) s = 0 := by
  simpa [pilotEvalSelect] using
    (pilotEvalWith_eq_zero_iff_ofPilotSeriesWith_eq_zero (surrealSemantics useNontrivial) s)

theorem pilotEvalSelect_false_eq_zero_iff_ofPilotSeriesSelect_eq_zero (s : PilotSeries) :
    pilotEvalSelect false s = 0 ↔
      ofPilotSeriesSelect false s = 0 := by
  simpa using (pilotEvalSelect_eq_zero_iff_ofPilotSeriesSelect_eq_zero false s)

theorem pilotEvalSelect_add_cancel_left (useNontrivial : Bool) (x y z : PilotSeries) :
    pilotEvalSelect useNontrivial (HeytingLean.Numbers.Surreal.Hyperseries.add x y) =
      pilotEvalSelect useNontrivial (HeytingLean.Numbers.Surreal.Hyperseries.add x z) ↔
        pilotEvalSelect useNontrivial y = pilotEvalSelect useNontrivial z := by
  constructor
  · intro h
    exact add_left_cancel (a := pilotEvalSelect useNontrivial x) (by simpa [pilotEvalSelect_add] using h)
  · intro h
    simp [pilotEvalSelect_add, h]

theorem pilotEvalSelect_add_cancel_right (useNontrivial : Bool) (x y z : PilotSeries) :
    pilotEvalSelect useNontrivial (HeytingLean.Numbers.Surreal.Hyperseries.add y x) =
      pilotEvalSelect useNontrivial (HeytingLean.Numbers.Surreal.Hyperseries.add z x) ↔
        pilotEvalSelect useNontrivial y = pilotEvalSelect useNontrivial z := by
  constructor
  · intro h
    exact add_right_cancel (b := pilotEvalSelect useNontrivial x) (by simpa [pilotEvalSelect_add] using h)
  · intro h
    simp [pilotEvalSelect_add, h]

theorem pilotEvalSelect_mul_monomial_eq_zero_of_coeff_mul_eq_zero
    (useNontrivial : Bool) (c₁ c₂ : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF)
    (hcoeff : c₁ * c₂ = 0) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₁ e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₂ e₂)) = 0 := by
  rw [pilotEvalSelect_mul_monomial useNontrivial c₁ c₂ e₁ e₂]
  simp [hcoeff]

theorem pilotEvalSelect_false_mul_monomial_eq_zero_of_coeff_mul_eq_zero
    (c₁ c₂ : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF)
    (hcoeff : c₁ * c₂ = 0) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₁ e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₂ e₂)) = 0 := by
  exact pilotEvalSelect_mul_monomial_eq_zero_of_coeff_mul_eq_zero false c₁ c₂ e₁ e₂ hcoeff

theorem pilotEvalSelect_mul_monomial_eq_zero_iff
    (useNontrivial : Bool) (c₁ c₂ : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₁ e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₂ e₂)) = 0 ↔
      pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.monomial (c₁ * c₂) (e₁ + e₂)) = 0 := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₁ e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₂ e₂)) = 0 ↔
      pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.monomial (c₁ * c₂) (e₁ + e₂)) = 0
  exact pilotEvalWith_mul_monomial_eq_zero_iff (surrealSemantics useNontrivial) c₁ c₂ e₁ e₂

theorem pilotEvalSelect_false_mul_monomial_eq_zero_iff
    (c₁ c₂ : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₁ e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₂ e₂)) = 0 ↔
      pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.monomial (c₁ * c₂) (e₁ + e₂)) = 0 := by
  exact pilotEvalSelect_mul_monomial_eq_zero_iff false c₁ c₂ e₁ e₂

theorem pilotEvalSelect_add_mul_monomial_zero_left_lhs
    (useNontrivial : Bool)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) = pilotEvalSelect useNontrivial s := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) = pilotEvalWith (surrealSemantics useNontrivial) s
  exact pilotEvalWith_add_mul_monomial_zero_left_lhs (surrealSemantics useNontrivial) c e₁ e₂ s

theorem pilotEvalSelect_add_mul_monomial_zero_right_lhs
    (useNontrivial : Bool)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) = pilotEvalSelect useNontrivial s := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) = pilotEvalWith (surrealSemantics useNontrivial) s
  exact pilotEvalWith_add_mul_monomial_zero_right_lhs (surrealSemantics useNontrivial) c e₁ e₂ s

theorem pilotEvalSelect_add_mul_monomial_zero_left_rhs
    (useNontrivial : Bool)
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) =
      pilotEvalSelect useNontrivial s := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) =
      pilotEvalWith (surrealSemantics useNontrivial) s
  exact pilotEvalWith_add_mul_monomial_zero_left_rhs (surrealSemantics useNontrivial) s c e₁ e₂

theorem pilotEvalSelect_add_mul_monomial_zero_right_rhs
    (useNontrivial : Bool)
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) =
      pilotEvalSelect useNontrivial s := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) =
      pilotEvalWith (surrealSemantics useNontrivial) s
  exact pilotEvalWith_add_mul_monomial_zero_right_rhs (surrealSemantics useNontrivial) s c e₁ e₂

theorem pilotEvalSelect_add_mul_monomial_zero_left_lhs_eq_zero_iff
    (useNontrivial : Bool)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) = 0 ↔
      pilotEvalSelect useNontrivial s = 0 := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) = 0 ↔
      pilotEvalWith (surrealSemantics useNontrivial) s = 0
  exact pilotEvalWith_add_mul_monomial_zero_left_lhs_eq_zero_iff
    (surrealSemantics useNontrivial) c e₁ e₂ s

theorem pilotEvalSelect_add_mul_monomial_zero_right_lhs_eq_zero_iff
    (useNontrivial : Bool)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) = 0 ↔
      pilotEvalSelect useNontrivial s = 0 := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) = 0 ↔
      pilotEvalWith (surrealSemantics useNontrivial) s = 0
  exact pilotEvalWith_add_mul_monomial_zero_right_lhs_eq_zero_iff
    (surrealSemantics useNontrivial) c e₁ e₂ s

theorem pilotEvalSelect_add_mul_monomial_zero_left_rhs_eq_zero_iff
    (useNontrivial : Bool)
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) = 0 ↔
      pilotEvalSelect useNontrivial s = 0 := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) = 0 ↔
      pilotEvalWith (surrealSemantics useNontrivial) s = 0
  exact pilotEvalWith_add_mul_monomial_zero_left_rhs_eq_zero_iff
    (surrealSemantics useNontrivial) s c e₁ e₂

theorem pilotEvalSelect_add_mul_monomial_zero_right_rhs_eq_zero_iff
    (useNontrivial : Bool)
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) = 0 ↔
      pilotEvalSelect useNontrivial s = 0 := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) = 0 ↔
      pilotEvalWith (surrealSemantics useNontrivial) s = 0
  exact pilotEvalWith_add_mul_monomial_zero_right_rhs_eq_zero_iff
    (surrealSemantics useNontrivial) s c e₁ e₂

theorem pilotEvalSelect_add_mul_monomial_zero_left_lhs_eq_zero_iff_right
    (useNontrivial : Bool)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) = 0 ↔
      0 = pilotEvalSelect useNontrivial s := by
  constructor
  · intro h
    exact Eq.symm <| (pilotEvalSelect_add_mul_monomial_zero_left_lhs_eq_zero_iff useNontrivial c e₁ e₂ s).1 h
  · intro h
    exact (pilotEvalSelect_add_mul_monomial_zero_left_lhs_eq_zero_iff useNontrivial c e₁ e₂ s).2 (Eq.symm h)

theorem pilotEvalSelect_add_mul_monomial_zero_right_lhs_eq_zero_iff_right
    (useNontrivial : Bool)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) = 0 ↔
      0 = pilotEvalSelect useNontrivial s := by
  constructor
  · intro h
    exact Eq.symm <| (pilotEvalSelect_add_mul_monomial_zero_right_lhs_eq_zero_iff useNontrivial c e₁ e₂ s).1 h
  · intro h
    exact (pilotEvalSelect_add_mul_monomial_zero_right_lhs_eq_zero_iff useNontrivial c e₁ e₂ s).2 (Eq.symm h)

theorem pilotEvalSelect_add_mul_monomial_zero_left_rhs_eq_zero_iff_right
    (useNontrivial : Bool)
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) = 0 ↔
      0 = pilotEvalSelect useNontrivial s := by
  constructor
  · intro h
    exact Eq.symm <| (pilotEvalSelect_add_mul_monomial_zero_left_rhs_eq_zero_iff useNontrivial s c e₁ e₂).1 h
  · intro h
    exact (pilotEvalSelect_add_mul_monomial_zero_left_rhs_eq_zero_iff useNontrivial s c e₁ e₂).2 (Eq.symm h)

theorem pilotEvalSelect_add_mul_monomial_zero_right_rhs_eq_zero_iff_right
    (useNontrivial : Bool)
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) = 0 ↔
      0 = pilotEvalSelect useNontrivial s := by
  constructor
  · intro h
    exact Eq.symm <| (pilotEvalSelect_add_mul_monomial_zero_right_rhs_eq_zero_iff useNontrivial s c e₁ e₂).1 h
  · intro h
    exact (pilotEvalSelect_add_mul_monomial_zero_right_rhs_eq_zero_iff useNontrivial s c e₁ e₂).2 (Eq.symm h)

theorem pilotEvalSelect_add_mul_monomial_zero_left_lhs_eq_zero_iff_left
    (useNontrivial : Bool)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    0 =
        pilotEvalSelect useNontrivial
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
            s) ↔
      0 = pilotEvalSelect useNontrivial s := by
  constructor
  · intro h
    exact Eq.symm <| (pilotEvalSelect_add_mul_monomial_zero_left_lhs_eq_zero_iff useNontrivial c e₁ e₂ s).1 (Eq.symm h)
  · intro h
    exact Eq.symm <| (pilotEvalSelect_add_mul_monomial_zero_left_lhs_eq_zero_iff useNontrivial c e₁ e₂ s).2 (Eq.symm h)

theorem pilotEvalSelect_add_mul_monomial_zero_right_lhs_eq_zero_iff_left
    (useNontrivial : Bool)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    0 =
        pilotEvalSelect useNontrivial
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
            s) ↔
      0 = pilotEvalSelect useNontrivial s := by
  constructor
  · intro h
    exact Eq.symm <| (pilotEvalSelect_add_mul_monomial_zero_right_lhs_eq_zero_iff useNontrivial c e₁ e₂ s).1 (Eq.symm h)
  · intro h
    exact Eq.symm <| (pilotEvalSelect_add_mul_monomial_zero_right_lhs_eq_zero_iff useNontrivial c e₁ e₂ s).2 (Eq.symm h)

theorem pilotEvalSelect_add_mul_monomial_zero_left_rhs_eq_zero_iff_left
    (useNontrivial : Bool)
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    0 =
        pilotEvalSelect useNontrivial
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            s
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) ↔
      0 = pilotEvalSelect useNontrivial s := by
  constructor
  · intro h
    exact Eq.symm <| (pilotEvalSelect_add_mul_monomial_zero_left_rhs_eq_zero_iff useNontrivial s c e₁ e₂).1 (Eq.symm h)
  · intro h
    exact Eq.symm <| (pilotEvalSelect_add_mul_monomial_zero_left_rhs_eq_zero_iff useNontrivial s c e₁ e₂).2 (Eq.symm h)

theorem pilotEvalSelect_add_mul_monomial_zero_right_rhs_eq_zero_iff_left
    (useNontrivial : Bool)
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    0 =
        pilotEvalSelect useNontrivial
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            s
            (HeytingLean.Numbers.Surreal.Hyperseries.mul
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
              (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) ↔
      0 = pilotEvalSelect useNontrivial s := by
  constructor
  · intro h
    exact Eq.symm <| (pilotEvalSelect_add_mul_monomial_zero_right_rhs_eq_zero_iff useNontrivial s c e₁ e₂).1 (Eq.symm h)
  · intro h
    exact Eq.symm <| (pilotEvalSelect_add_mul_monomial_zero_right_rhs_eq_zero_iff useNontrivial s c e₁ e₂).2 (Eq.symm h)

theorem pilotEvalSelect_add_mul_monomial_zero_left_lhs_eq_iff
    (useNontrivial : Bool)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) =
      pilotEvalSelect useNontrivial t ↔
      pilotEvalSelect useNontrivial s = pilotEvalSelect useNontrivial t := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) =
      pilotEvalWith (surrealSemantics useNontrivial) t ↔
      pilotEvalWith (surrealSemantics useNontrivial) s =
        pilotEvalWith (surrealSemantics useNontrivial) t
  exact pilotEvalWith_add_mul_monomial_zero_left_lhs_eq_iff
    (surrealSemantics useNontrivial) c e₁ e₂ s t

theorem pilotEvalSelect_add_mul_monomial_zero_right_lhs_eq_iff
    (useNontrivial : Bool)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) =
      pilotEvalSelect useNontrivial t ↔
      pilotEvalSelect useNontrivial s = pilotEvalSelect useNontrivial t := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) =
      pilotEvalWith (surrealSemantics useNontrivial) t ↔
      pilotEvalWith (surrealSemantics useNontrivial) s =
        pilotEvalWith (surrealSemantics useNontrivial) t
  exact pilotEvalWith_add_mul_monomial_zero_right_lhs_eq_iff
    (surrealSemantics useNontrivial) c e₁ e₂ s t

theorem pilotEvalSelect_add_mul_monomial_zero_left_rhs_eq_iff
    (useNontrivial : Bool)
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) =
      pilotEvalSelect useNontrivial t ↔
      pilotEvalSelect useNontrivial s = pilotEvalSelect useNontrivial t := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) =
      pilotEvalWith (surrealSemantics useNontrivial) t ↔
      pilotEvalWith (surrealSemantics useNontrivial) s =
        pilotEvalWith (surrealSemantics useNontrivial) t
  exact pilotEvalWith_add_mul_monomial_zero_left_rhs_eq_iff
    (surrealSemantics useNontrivial) s t c e₁ e₂

theorem pilotEvalSelect_add_mul_monomial_zero_right_rhs_eq_iff
    (useNontrivial : Bool)
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) =
      pilotEvalSelect useNontrivial t ↔
      pilotEvalSelect useNontrivial s = pilotEvalSelect useNontrivial t := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) =
      pilotEvalWith (surrealSemantics useNontrivial) t ↔
      pilotEvalWith (surrealSemantics useNontrivial) s =
        pilotEvalWith (surrealSemantics useNontrivial) t
  exact pilotEvalWith_add_mul_monomial_zero_right_rhs_eq_iff
    (surrealSemantics useNontrivial) s t c e₁ e₂

theorem pilotEvalSelect_add_mul_monomial_zero_left_lhs_eq_iff_right
    (useNontrivial : Bool)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) =
      pilotEvalSelect useNontrivial t ↔
      pilotEvalSelect useNontrivial t = pilotEvalSelect useNontrivial s := by
  constructor
  · intro h
    exact Eq.symm <|
      (pilotEvalSelect_add_mul_monomial_zero_left_lhs_eq_iff useNontrivial c e₁ e₂ s t).1 h
  · intro h
    exact (pilotEvalSelect_add_mul_monomial_zero_left_lhs_eq_iff useNontrivial c e₁ e₂ s t).2 (Eq.symm h)

theorem pilotEvalSelect_add_mul_monomial_zero_right_lhs_eq_iff_right
    (useNontrivial : Bool)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) =
      pilotEvalSelect useNontrivial t ↔
      pilotEvalSelect useNontrivial t = pilotEvalSelect useNontrivial s := by
  constructor
  · intro h
    exact Eq.symm <|
      (pilotEvalSelect_add_mul_monomial_zero_right_lhs_eq_iff useNontrivial c e₁ e₂ s t).1 h
  · intro h
    exact (pilotEvalSelect_add_mul_monomial_zero_right_lhs_eq_iff useNontrivial c e₁ e₂ s t).2 (Eq.symm h)

theorem pilotEvalSelect_add_mul_monomial_zero_left_rhs_eq_iff_right
    (useNontrivial : Bool)
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) =
      pilotEvalSelect useNontrivial t ↔
      pilotEvalSelect useNontrivial t = pilotEvalSelect useNontrivial s := by
  constructor
  · intro h
    exact Eq.symm <|
      (pilotEvalSelect_add_mul_monomial_zero_left_rhs_eq_iff useNontrivial s t c e₁ e₂).1 h
  · intro h
    exact (pilotEvalSelect_add_mul_monomial_zero_left_rhs_eq_iff useNontrivial s t c e₁ e₂).2 (Eq.symm h)

theorem pilotEvalSelect_add_mul_monomial_zero_right_rhs_eq_iff_right
    (useNontrivial : Bool)
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) =
      pilotEvalSelect useNontrivial t ↔
      pilotEvalSelect useNontrivial t = pilotEvalSelect useNontrivial s := by
  constructor
  · intro h
    exact Eq.symm <|
      (pilotEvalSelect_add_mul_monomial_zero_right_rhs_eq_iff useNontrivial s t c e₁ e₂).1 h
  · intro h
    exact (pilotEvalSelect_add_mul_monomial_zero_right_rhs_eq_iff useNontrivial s t c e₁ e₂).2 (Eq.symm h)

theorem pilotEvalSelect_add_mul_monomial_zero_left_lhs_eq_iff_left
    (useNontrivial : Bool)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalSelect useNontrivial t =
      pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) ↔
      pilotEvalSelect useNontrivial t = pilotEvalSelect useNontrivial s := by
  constructor
  · intro h
    exact Eq.symm <|
      (pilotEvalSelect_add_mul_monomial_zero_left_lhs_eq_iff useNontrivial c e₁ e₂ s t).1 (Eq.symm h)
  · intro h
    exact Eq.symm <|
      (pilotEvalSelect_add_mul_monomial_zero_left_lhs_eq_iff useNontrivial c e₁ e₂ s t).2 (Eq.symm h)

theorem pilotEvalSelect_add_mul_monomial_zero_right_lhs_eq_iff_left
    (useNontrivial : Bool)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalSelect useNontrivial t =
      pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) ↔
      pilotEvalSelect useNontrivial t = pilotEvalSelect useNontrivial s := by
  constructor
  · intro h
    exact Eq.symm <|
      (pilotEvalSelect_add_mul_monomial_zero_right_lhs_eq_iff useNontrivial c e₁ e₂ s t).1 (Eq.symm h)
  · intro h
    exact Eq.symm <|
      (pilotEvalSelect_add_mul_monomial_zero_right_lhs_eq_iff useNontrivial c e₁ e₂ s t).2 (Eq.symm h)

theorem pilotEvalSelect_add_mul_monomial_zero_left_rhs_eq_iff_left
    (useNontrivial : Bool)
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect useNontrivial t =
      pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) ↔
      pilotEvalSelect useNontrivial t = pilotEvalSelect useNontrivial s := by
  constructor
  · intro h
    exact Eq.symm <|
      (pilotEvalSelect_add_mul_monomial_zero_left_rhs_eq_iff useNontrivial s t c e₁ e₂).1 (Eq.symm h)
  · intro h
    exact Eq.symm <|
      (pilotEvalSelect_add_mul_monomial_zero_left_rhs_eq_iff useNontrivial s t c e₁ e₂).2 (Eq.symm h)

theorem pilotEvalSelect_add_mul_monomial_zero_right_rhs_eq_iff_left
    (useNontrivial : Bool)
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect useNontrivial t =
      pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) ↔
      pilotEvalSelect useNontrivial t = pilotEvalSelect useNontrivial s := by
  constructor
  · intro h
    exact Eq.symm <|
      (pilotEvalSelect_add_mul_monomial_zero_right_rhs_eq_iff useNontrivial s t c e₁ e₂).1 (Eq.symm h)
  · intro h
    exact Eq.symm <|
      (pilotEvalSelect_add_mul_monomial_zero_right_rhs_eq_iff useNontrivial s t c e₁ e₂).2 (Eq.symm h)

theorem pilotEvalSelect_add_mul_monomial_zero_left_lhs_cancel
    (useNontrivial : Bool)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) =
      pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          t) ↔
      pilotEvalSelect useNontrivial s = pilotEvalSelect useNontrivial t := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) =
      pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          t) ↔
      pilotEvalWith (surrealSemantics useNontrivial) s =
        pilotEvalWith (surrealSemantics useNontrivial) t
  exact pilotEvalWith_add_mul_monomial_zero_left_lhs_cancel
    (surrealSemantics useNontrivial) c e₁ e₂ s t

theorem pilotEvalSelect_add_mul_monomial_zero_right_lhs_cancel
    (useNontrivial : Bool)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) =
      pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          t) ↔
      pilotEvalSelect useNontrivial s = pilotEvalSelect useNontrivial t := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) =
      pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          t) ↔
      pilotEvalWith (surrealSemantics useNontrivial) s =
        pilotEvalWith (surrealSemantics useNontrivial) t
  exact pilotEvalWith_add_mul_monomial_zero_right_lhs_cancel
    (surrealSemantics useNontrivial) c e₁ e₂ s t

theorem pilotEvalSelect_add_mul_monomial_zero_left_rhs_cancel
    (useNontrivial : Bool)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) =
      pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          t
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) ↔
      pilotEvalSelect useNontrivial s = pilotEvalSelect useNontrivial t := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) =
      pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          t
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) ↔
      pilotEvalWith (surrealSemantics useNontrivial) s =
        pilotEvalWith (surrealSemantics useNontrivial) t
  exact pilotEvalWith_add_mul_monomial_zero_left_rhs_cancel
    (surrealSemantics useNontrivial) c e₁ e₂ s t

theorem pilotEvalSelect_add_mul_monomial_zero_right_rhs_cancel
    (useNontrivial : Bool)
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) =
      pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          t
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) ↔
      pilotEvalSelect useNontrivial s = pilotEvalSelect useNontrivial t := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) =
      pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          t
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) ↔
      pilotEvalWith (surrealSemantics useNontrivial) s =
        pilotEvalWith (surrealSemantics useNontrivial) t
  exact pilotEvalWith_add_mul_monomial_zero_right_rhs_cancel
    (surrealSemantics useNontrivial) c e₁ e₂ s t

theorem pilotEvalSelect_false_add_mul_monomial_zero_left_lhs
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) = pilotEvalSelect false s := by
  exact pilotEvalSelect_add_mul_monomial_zero_left_lhs false c e₁ e₂ s

theorem pilotEvalSelect_false_add_mul_monomial_zero_right_lhs
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) = pilotEvalSelect false s := by
  exact pilotEvalSelect_add_mul_monomial_zero_right_lhs false c e₁ e₂ s

theorem pilotEvalSelect_false_add_mul_monomial_zero_left_rhs
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) =
      pilotEvalSelect false s := by
  exact pilotEvalSelect_add_mul_monomial_zero_left_rhs false s c e₁ e₂

theorem pilotEvalSelect_false_add_mul_monomial_zero_right_rhs
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) =
      pilotEvalSelect false s := by
  exact pilotEvalSelect_add_mul_monomial_zero_right_rhs false s c e₁ e₂

theorem pilotEvalSelect_false_add_mul_monomial_zero_left_lhs_eq_zero_iff
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) = 0 ↔
      pilotEvalSelect false s = 0 := by
  exact pilotEvalSelect_add_mul_monomial_zero_left_lhs_eq_zero_iff false c e₁ e₂ s

theorem pilotEvalSelect_false_add_mul_monomial_zero_right_lhs_eq_zero_iff
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) = 0 ↔
      pilotEvalSelect false s = 0 := by
  exact pilotEvalSelect_add_mul_monomial_zero_right_lhs_eq_zero_iff false c e₁ e₂ s

theorem pilotEvalSelect_false_add_mul_monomial_zero_left_rhs_eq_zero_iff
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) = 0 ↔
      pilotEvalSelect false s = 0 := by
  exact pilotEvalSelect_add_mul_monomial_zero_left_rhs_eq_zero_iff false s c e₁ e₂

theorem pilotEvalSelect_false_add_mul_monomial_zero_right_rhs_eq_zero_iff
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) = 0 ↔
      pilotEvalSelect false s = 0 := by
  exact pilotEvalSelect_add_mul_monomial_zero_right_rhs_eq_zero_iff false s c e₁ e₂

theorem pilotEvalSelect_false_add_mul_monomial_zero_left_lhs_eq_zero_iff_right
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) = 0 ↔
      0 = pilotEvalSelect false s := by
  exact pilotEvalSelect_add_mul_monomial_zero_left_lhs_eq_zero_iff_right false c e₁ e₂ s

theorem pilotEvalSelect_false_add_mul_monomial_zero_right_lhs_eq_zero_iff_right
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) = 0 ↔
      0 = pilotEvalSelect false s := by
  exact pilotEvalSelect_add_mul_monomial_zero_right_lhs_eq_zero_iff_right false c e₁ e₂ s

theorem pilotEvalSelect_false_add_mul_monomial_zero_left_rhs_eq_zero_iff_right
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) = 0 ↔
      0 = pilotEvalSelect false s := by
  exact pilotEvalSelect_add_mul_monomial_zero_left_rhs_eq_zero_iff_right false s c e₁ e₂

theorem pilotEvalSelect_false_add_mul_monomial_zero_right_rhs_eq_zero_iff_right
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) = 0 ↔
      0 = pilotEvalSelect false s := by
  exact pilotEvalSelect_add_mul_monomial_zero_right_rhs_eq_zero_iff_right false s c e₁ e₂

theorem pilotEvalSelect_false_add_mul_monomial_zero_left_lhs_eq_zero_iff_left
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    0 =
      pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) ↔
      0 = pilotEvalSelect false s := by
  exact pilotEvalSelect_add_mul_monomial_zero_left_lhs_eq_zero_iff_left false c e₁ e₂ s

theorem pilotEvalSelect_false_add_mul_monomial_zero_right_lhs_eq_zero_iff_left
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    0 =
      pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) ↔
      0 = pilotEvalSelect false s := by
  exact pilotEvalSelect_add_mul_monomial_zero_right_lhs_eq_zero_iff_left false c e₁ e₂ s

theorem pilotEvalSelect_false_add_mul_monomial_zero_left_rhs_eq_zero_iff_left
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    0 =
      pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) ↔
      0 = pilotEvalSelect false s := by
  exact pilotEvalSelect_add_mul_monomial_zero_left_rhs_eq_zero_iff_left false s c e₁ e₂

theorem pilotEvalSelect_false_add_mul_monomial_zero_right_rhs_eq_zero_iff_left
    (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    0 =
      pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) ↔
      0 = pilotEvalSelect false s := by
  exact pilotEvalSelect_add_mul_monomial_zero_right_rhs_eq_zero_iff_left false s c e₁ e₂

theorem pilotEvalSelect_false_add_mul_monomial_zero_left_lhs_eq_iff
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) =
      pilotEvalSelect false t ↔
      pilotEvalSelect false s = pilotEvalSelect false t := by
  exact pilotEvalSelect_add_mul_monomial_zero_left_lhs_eq_iff false c e₁ e₂ s t

theorem pilotEvalSelect_false_add_mul_monomial_zero_right_lhs_eq_iff
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) =
      pilotEvalSelect false t ↔
      pilotEvalSelect false s = pilotEvalSelect false t := by
  exact pilotEvalSelect_add_mul_monomial_zero_right_lhs_eq_iff false c e₁ e₂ s t

theorem pilotEvalSelect_false_add_mul_monomial_zero_left_rhs_eq_iff
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) =
      pilotEvalSelect false t ↔
      pilotEvalSelect false s = pilotEvalSelect false t := by
  exact pilotEvalSelect_add_mul_monomial_zero_left_rhs_eq_iff false s t c e₁ e₂

theorem pilotEvalSelect_false_add_mul_monomial_zero_right_rhs_eq_iff
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) =
      pilotEvalSelect false t ↔
      pilotEvalSelect false s = pilotEvalSelect false t := by
  exact pilotEvalSelect_add_mul_monomial_zero_right_rhs_eq_iff false s t c e₁ e₂

theorem pilotEvalSelect_false_add_mul_monomial_zero_left_lhs_eq_iff_right
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) =
      pilotEvalSelect false t ↔
      pilotEvalSelect false t = pilotEvalSelect false s := by
  exact pilotEvalSelect_add_mul_monomial_zero_left_lhs_eq_iff_right false c e₁ e₂ s t

theorem pilotEvalSelect_false_add_mul_monomial_zero_right_lhs_eq_iff_right
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) =
      pilotEvalSelect false t ↔
      pilotEvalSelect false t = pilotEvalSelect false s := by
  exact pilotEvalSelect_add_mul_monomial_zero_right_lhs_eq_iff_right false c e₁ e₂ s t

theorem pilotEvalSelect_false_add_mul_monomial_zero_left_rhs_eq_iff_right
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) =
      pilotEvalSelect false t ↔
      pilotEvalSelect false t = pilotEvalSelect false s := by
  exact pilotEvalSelect_add_mul_monomial_zero_left_rhs_eq_iff_right false s t c e₁ e₂

theorem pilotEvalSelect_false_add_mul_monomial_zero_right_rhs_eq_iff_right
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) =
      pilotEvalSelect false t ↔
      pilotEvalSelect false t = pilotEvalSelect false s := by
  exact pilotEvalSelect_add_mul_monomial_zero_right_rhs_eq_iff_right false s t c e₁ e₂

theorem pilotEvalSelect_false_add_mul_monomial_zero_left_lhs_eq_iff_left
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalSelect false t =
      pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) ↔
      pilotEvalSelect false t = pilotEvalSelect false s := by
  exact pilotEvalSelect_add_mul_monomial_zero_left_lhs_eq_iff_left false c e₁ e₂ s t

theorem pilotEvalSelect_false_add_mul_monomial_zero_right_lhs_eq_iff_left
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalSelect false t =
      pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) ↔
      pilotEvalSelect false t = pilotEvalSelect false s := by
  exact pilotEvalSelect_add_mul_monomial_zero_right_lhs_eq_iff_left false c e₁ e₂ s t

theorem pilotEvalSelect_false_add_mul_monomial_zero_left_rhs_eq_iff_left
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect false t =
      pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) ↔
      pilotEvalSelect false t = pilotEvalSelect false s := by
  exact pilotEvalSelect_add_mul_monomial_zero_left_rhs_eq_iff_left false s t c e₁ e₂

theorem pilotEvalSelect_false_add_mul_monomial_zero_right_rhs_eq_iff_left
    (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect false t =
      pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) ↔
      pilotEvalSelect false t = pilotEvalSelect false s := by
  exact pilotEvalSelect_add_mul_monomial_zero_right_rhs_eq_iff_left false s t c e₁ e₂

theorem pilotEvalSelect_false_add_mul_monomial_zero_left_lhs_cancel
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) =
      pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          t) ↔
      pilotEvalSelect false s = pilotEvalSelect false t := by
  exact pilotEvalSelect_add_mul_monomial_zero_left_lhs_cancel false c e₁ e₂ s t

theorem pilotEvalSelect_false_add_mul_monomial_zero_right_lhs_cancel
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) =
      pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          t) ↔
      pilotEvalSelect false s = pilotEvalSelect false t := by
  exact pilotEvalSelect_add_mul_monomial_zero_right_lhs_cancel false c e₁ e₂ s t

theorem pilotEvalSelect_false_add_mul_monomial_zero_left_rhs_cancel
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) =
      pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          t
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) ↔
      pilotEvalSelect false s = pilotEvalSelect false t := by
  exact pilotEvalSelect_add_mul_monomial_zero_left_rhs_cancel false c e₁ e₂ s t

theorem pilotEvalSelect_false_add_mul_monomial_zero_right_rhs_cancel
    (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) =
      pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          t
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) ↔
      pilotEvalSelect false s = pilotEvalSelect false t := by
  exact pilotEvalSelect_add_mul_monomial_zero_right_rhs_cancel false c e₁ e₂ s t

theorem pilotEvalWith_eq_foldr (S : SurrealExpLogSemantics) (s : PilotSeries) :
    pilotEvalWith S s =
      s.foldr (fun t acc => BridgePilot.termSem (SurrealExpLogSemantics.toModel S) t + acc) 0 := by
  unfold pilotEvalWith
  rw [evalOmega_ofPilotSeriesWith]
  simpa using (BridgePilot.eval_ofSeries_eq_foldr (M := SurrealExpLogSemantics.toModel S) s)

theorem pilotEvalSelect_append_assoc (useNontrivial : Bool) (x y z : PilotSeries) :
    pilotEvalSelect useNontrivial ((x ++ y) ++ z) =
      pilotEvalSelect useNontrivial x +
        pilotEvalSelect useNontrivial y +
        pilotEvalSelect useNontrivial z := by
  simp [pilotEvalSelect_append, add_assoc]

theorem pilotEvalSelect_add_assoc (useNontrivial : Bool) (x y z : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.add x y) z) =
      pilotEvalSelect useNontrivial x +
        pilotEvalSelect useNontrivial y +
        pilotEvalSelect useNontrivial z := by
  simpa [HeytingLean.Numbers.Surreal.Hyperseries.add, List.append_assoc] using
    (pilotEvalSelect_append_assoc useNontrivial x y z)

theorem pilotEvalSelect_add_comm (useNontrivial : Bool) (x y : PilotSeries) :
    pilotEvalSelect useNontrivial (HeytingLean.Numbers.Surreal.Hyperseries.add x y) =
      pilotEvalSelect useNontrivial (HeytingLean.Numbers.Surreal.Hyperseries.add y x) := by
  simp [pilotEvalSelect_add, add_comm]

theorem pilotEval_eq_foldr (s : PilotSeries) :
    pilotEval s = s.foldr (fun t acc => BridgePilot.termSem surrealModel t + acc) 0 := by
  simpa [pilotEval, pilotEvalWith, surrealModel, instHyperserialModelSurreal, surrealSemanticsDefault] using
    (pilotEvalWith_eq_foldr surrealSemanticsDefault s)

theorem pilotEvalSelect_false_eq_foldr (s : PilotSeries) :
    pilotEvalSelect false s = s.foldr (fun t acc => BridgePilot.termSem surrealModel t + acc) 0 := by
  simpa [pilotEvalSelect_false_eq_pilotEval] using (pilotEval_eq_foldr s)

theorem pilotEvalSelect_false_append_assoc (x y z : PilotSeries) :
    pilotEvalSelect false ((x ++ y) ++ z) =
      pilotEvalSelect false x + pilotEvalSelect false y + pilotEvalSelect false z := by
  exact pilotEvalSelect_append_assoc false x y z

theorem pilotEvalSelect_false_add_assoc (x y z : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.add x y) z) =
      pilotEvalSelect false x + pilotEvalSelect false y + pilotEvalSelect false z := by
  exact pilotEvalSelect_add_assoc false x y z

theorem pilotEvalSelect_false_add_comm (x y : PilotSeries) :
    pilotEvalSelect false (HeytingLean.Numbers.Surreal.Hyperseries.add x y) =
      pilotEvalSelect false (HeytingLean.Numbers.Surreal.Hyperseries.add y x) := by
  exact pilotEvalSelect_add_comm false x y

theorem pilotEval_append_assoc (x y z : PilotSeries) :
    pilotEval ((x ++ y) ++ z) = pilotEval x + pilotEval y + pilotEval z := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_append_assoc surrealSemanticsDefault x y z)

theorem pilotEval_add_assoc (x y z : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.add x y) z) =
      pilotEval x + pilotEval y + pilotEval z := by
  simpa [HeytingLean.Numbers.Surreal.Hyperseries.add, List.append_assoc, add_assoc] using
    (pilotEval_append_assoc x y z)

theorem pilotEval_add_comm (x y : PilotSeries) :
    pilotEval (HeytingLean.Numbers.Surreal.Hyperseries.add x y) =
      pilotEval (HeytingLean.Numbers.Surreal.Hyperseries.add y x) := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_comm surrealSemanticsDefault x y)

theorem ofPilotSeries_eq_zero_of_pilotEval_eq_zero {s : PilotSeries}
    (h : pilotEval s = 0) : ofPilotSeries s = 0 := by
  exact (ofPilotSeries_eq_iff_evalOmega_eq s []).2 (by simpa [pilotEval, ofPilotSeries_nil] using h)

theorem pilotEval_eq_zero_of_ofPilotSeries_eq_zero {s : PilotSeries}
    (h : ofPilotSeries s = 0) : pilotEval s = 0 := by
  simpa [pilotEval] using congrArg evalOmega h

theorem pilotEval_eq_zero_iff_ofPilotSeries_eq_zero (s : PilotSeries) :
    pilotEval s = 0 ↔ ofPilotSeries s = 0 := by
  constructor
  · exact ofPilotSeries_eq_zero_of_pilotEval_eq_zero
  · exact pilotEval_eq_zero_of_ofPilotSeries_eq_zero

theorem pilotEval_eq_zero_iff_ofPilotSeriesWith_eq_zero (s : PilotSeries) :
    pilotEval s = 0 ↔ ofPilotSeriesWith surrealSemanticsDefault s = 0 := by
  simpa [ofPilotSeries] using (pilotEval_eq_zero_iff_ofPilotSeries_eq_zero s)

theorem pilotEvalSelect_false_eq_zero_iff_ofPilotSeries_eq_zero (s : PilotSeries) :
    pilotEvalSelect false s = 0 ↔ ofPilotSeries s = 0 := by
  simpa [pilotEvalSelect_false_eq_pilotEval] using (pilotEval_eq_zero_iff_ofPilotSeries_eq_zero s)

theorem pilotEvalSelect_false_eq_zero_iff_ofPilotSeriesWith_eq_zero (s : PilotSeries) :
    pilotEvalSelect false s = 0 ↔ ofPilotSeriesWith surrealSemanticsDefault s = 0 := by
  simpa [pilotEvalSelect_false_eq_pilotEval] using (pilotEval_eq_zero_iff_ofPilotSeriesWith_eq_zero s)

theorem pilotEvalSelect_eq_zero_iff_ofPilotSeries_eq_zero (s : PilotSeries) :
    pilotEvalSelect false s = 0 ↔ ofPilotSeries s = 0 := by
  exact pilotEvalSelect_false_eq_zero_iff_ofPilotSeries_eq_zero s

theorem pilotEval_eq_zero_iff_ofPilotSeriesSelect_false_eq_zero (s : PilotSeries) :
    pilotEval s = 0 ↔ ofPilotSeriesSelect false s = 0 := by
  simpa [pilotEvalSelect_false_eq_pilotEval] using
    (pilotEvalSelect_false_eq_zero_iff_ofPilotSeriesSelect_eq_zero s)

theorem pilotEvalWith_add_cancel_left (S : SurrealExpLogSemantics) (x y z : PilotSeries) :
    pilotEvalWith S (HeytingLean.Numbers.Surreal.Hyperseries.add x y) =
      pilotEvalWith S (HeytingLean.Numbers.Surreal.Hyperseries.add x z) ↔
        pilotEvalWith S y = pilotEvalWith S z := by
  constructor
  · intro h
    exact add_left_cancel (a := pilotEvalWith S x) (by simpa [pilotEvalWith_add] using h)
  · intro h
    simp [pilotEvalWith_add, h]

theorem pilotEvalWith_add_cancel_right (S : SurrealExpLogSemantics) (x y z : PilotSeries) :
    pilotEvalWith S (HeytingLean.Numbers.Surreal.Hyperseries.add y x) =
      pilotEvalWith S (HeytingLean.Numbers.Surreal.Hyperseries.add z x) ↔
        pilotEvalWith S y = pilotEvalWith S z := by
  constructor
  · intro h
    exact add_right_cancel (b := pilotEvalWith S x) (by simpa [pilotEvalWith_add] using h)
  · intro h
    simp [pilotEvalWith_add, h]

theorem pilotEvalWith_add_eq_zero_iff (S : SurrealExpLogSemantics) (x y : PilotSeries) :
    pilotEvalWith S (HeytingLean.Numbers.Surreal.Hyperseries.add x y) = 0 ↔
      pilotEvalWith S y = -(pilotEvalWith S x) := by
  constructor
  · intro h
    have hxy : pilotEvalWith S x + pilotEvalWith S y = 0 := by
      simpa [pilotEvalWith_add] using h
    have hyx : pilotEvalWith S y + pilotEvalWith S x = 0 := by
      simpa [add_comm] using hxy
    exact (eq_neg_iff_add_eq_zero).2 hyx
  · intro h
    have hyx : pilotEvalWith S y + pilotEvalWith S x = 0 :=
      (eq_neg_iff_add_eq_zero).1 h
    have hxy : pilotEvalWith S x + pilotEvalWith S y = 0 := by
      simpa [add_comm] using hyx
    simpa [pilotEvalWith_add] using hxy

theorem pilotEvalWith_add_eq_zero_iff_left (S : SurrealExpLogSemantics) (x y : PilotSeries) :
    pilotEvalWith S (HeytingLean.Numbers.Surreal.Hyperseries.add x y) = 0 ↔
      pilotEvalWith S x = -(pilotEvalWith S y) := by
  constructor
  · intro h
    have hyx : pilotEvalWith S y = -(pilotEvalWith S x) :=
      (pilotEvalWith_add_eq_zero_iff S x y).1 h
    have hyx' : pilotEvalWith S y + pilotEvalWith S x = 0 :=
      (eq_neg_iff_add_eq_zero).1 hyx
    have hxy : pilotEvalWith S x + pilotEvalWith S y = 0 := by
      simpa [add_comm] using hyx'
    exact (eq_neg_iff_add_eq_zero).2 hxy
  · intro h
    have hxy : pilotEvalWith S x + pilotEvalWith S y = 0 :=
      (eq_neg_iff_add_eq_zero).1 h
    have hyx : pilotEvalWith S y + pilotEvalWith S x = 0 := by
      simpa [add_comm] using hxy
    have hyx' : pilotEvalWith S y = -(pilotEvalWith S x) :=
      (eq_neg_iff_add_eq_zero).2 hyx
    exact (pilotEvalWith_add_eq_zero_iff S x y).2 hyx'

theorem pilotEvalWith_add_eq_zero_iff_right (S : SurrealExpLogSemantics) (x y : PilotSeries) :
    pilotEvalWith S (HeytingLean.Numbers.Surreal.Hyperseries.add x y) = 0 ↔
      -(pilotEvalWith S x) = pilotEvalWith S y := by
  constructor
  · intro h
    exact Eq.symm ((pilotEvalWith_add_eq_zero_iff S x y).1 h)
  · intro h
    exact (pilotEvalWith_add_eq_zero_iff S x y).2 (Eq.symm h)

theorem pilotEvalWith_add_normalize_left_eq_zero_iff
    (S : SurrealExpLogSemantics) (x y : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) = 0 ↔
      pilotEvalWith S y = -(pilotEvalWith S x) := by
  simpa [pilotEvalWith_normalize] using
    (pilotEvalWith_add_eq_zero_iff S (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y)

theorem pilotEvalWith_add_normalize_left_eq_zero_iff_left
    (S : SurrealExpLogSemantics) (x y : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) = 0 ↔
      pilotEvalWith S x = -(pilotEvalWith S y) := by
  simpa [pilotEvalWith_normalize] using
    (pilotEvalWith_add_eq_zero_iff_left S
      (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y)

theorem pilotEvalWith_add_normalize_left_eq_zero_iff_right
    (S : SurrealExpLogSemantics) (x y : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) = 0 ↔
      -(pilotEvalWith S x) = pilotEvalWith S y := by
  constructor
  · intro h
    exact Eq.symm ((pilotEvalWith_add_normalize_left_eq_zero_iff S x y).1 h)
  · intro h
    exact (pilotEvalWith_add_normalize_left_eq_zero_iff S x y).2 (Eq.symm h)

theorem pilotEvalWith_add_normalize_right_eq_zero_iff
    (S : SurrealExpLogSemantics) (x y : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEvalWith S y = -(pilotEvalWith S x) := by
  simpa [pilotEvalWith_normalize] using
    (pilotEvalWith_add_eq_zero_iff S x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y))

theorem pilotEvalWith_add_normalize_right_eq_zero_iff_left
    (S : SurrealExpLogSemantics) (x y : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEvalWith S x = -(pilotEvalWith S y) := by
  simpa [pilotEvalWith_normalize] using
    (pilotEvalWith_add_eq_zero_iff_left S x
      (HeytingLean.Numbers.Surreal.Hyperseries.normalize y))

theorem pilotEvalWith_add_normalize_right_eq_zero_iff_right
    (S : SurrealExpLogSemantics) (x y : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      -(pilotEvalWith S x) = pilotEvalWith S y := by
  constructor
  · intro h
    exact Eq.symm ((pilotEvalWith_add_normalize_right_eq_zero_iff S x y).1 h)
  · intro h
    exact (pilotEvalWith_add_normalize_right_eq_zero_iff S x y).2 (Eq.symm h)

theorem pilotEvalWith_add_normalize_eq_zero_iff
    (S : SurrealExpLogSemantics) (x y : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEvalWith S y = -(pilotEvalWith S x) := by
  simpa [pilotEvalWith_normalize] using
    (pilotEvalWith_add_eq_zero_iff S
      (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
      (HeytingLean.Numbers.Surreal.Hyperseries.normalize y))

theorem pilotEvalWith_add_normalize_eq_zero_iff_left
    (S : SurrealExpLogSemantics) (x y : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEvalWith S x = -(pilotEvalWith S y) := by
  simpa [pilotEvalWith_normalize] using
    (pilotEvalWith_add_eq_zero_iff_left S
      (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
      (HeytingLean.Numbers.Surreal.Hyperseries.normalize y))

theorem pilotEvalWith_add_normalize_eq_zero_iff_right
    (S : SurrealExpLogSemantics) (x y : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      -(pilotEvalWith S x) = pilotEvalWith S y := by
  constructor
  · intro h
    exact Eq.symm ((pilotEvalWith_add_normalize_eq_zero_iff S x y).1 h)
  · intro h
    exact (pilotEvalWith_add_normalize_eq_zero_iff S x y).2 (Eq.symm h)

theorem pilotEvalSelect_add_eq_zero_iff (useNontrivial : Bool) (x y : PilotSeries) :
    pilotEvalSelect useNontrivial (HeytingLean.Numbers.Surreal.Hyperseries.add x y) = 0 ↔
      pilotEvalSelect useNontrivial y = -(pilotEvalSelect useNontrivial x) := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add x y) = 0 ↔
      pilotEvalWith (surrealSemantics useNontrivial) y =
        -(pilotEvalWith (surrealSemantics useNontrivial) x)
  exact pilotEvalWith_add_eq_zero_iff (surrealSemantics useNontrivial) x y

theorem pilotEvalSelect_add_eq_zero_iff_left (useNontrivial : Bool) (x y : PilotSeries) :
    pilotEvalSelect useNontrivial (HeytingLean.Numbers.Surreal.Hyperseries.add x y) = 0 ↔
      pilotEvalSelect useNontrivial x = -(pilotEvalSelect useNontrivial y) := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add x y) = 0 ↔
      pilotEvalWith (surrealSemantics useNontrivial) x =
        -(pilotEvalWith (surrealSemantics useNontrivial) y)
  exact pilotEvalWith_add_eq_zero_iff_left (surrealSemantics useNontrivial) x y

theorem pilotEvalSelect_add_eq_zero_iff_right (useNontrivial : Bool) (x y : PilotSeries) :
    pilotEvalSelect useNontrivial (HeytingLean.Numbers.Surreal.Hyperseries.add x y) = 0 ↔
      -(pilotEvalSelect useNontrivial x) = pilotEvalSelect useNontrivial y := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add x y) = 0 ↔
      -(pilotEvalWith (surrealSemantics useNontrivial) x) =
        pilotEvalWith (surrealSemantics useNontrivial) y
  exact pilotEvalWith_add_eq_zero_iff_right (surrealSemantics useNontrivial) x y

theorem pilotEvalSelect_add_normalize_eq_zero_iff (useNontrivial : Bool) (x y : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEvalSelect useNontrivial y = -(pilotEvalSelect useNontrivial x) := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEvalWith (surrealSemantics useNontrivial) y =
        -(pilotEvalWith (surrealSemantics useNontrivial) x)
  exact pilotEvalWith_add_normalize_eq_zero_iff (surrealSemantics useNontrivial) x y

theorem pilotEvalSelect_add_normalize_eq_zero_iff_left (useNontrivial : Bool) (x y : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEvalSelect useNontrivial x = -(pilotEvalSelect useNontrivial y) := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEvalWith (surrealSemantics useNontrivial) x =
        -(pilotEvalWith (surrealSemantics useNontrivial) y)
  exact pilotEvalWith_add_normalize_eq_zero_iff_left (surrealSemantics useNontrivial) x y

theorem pilotEvalSelect_add_normalize_eq_zero_iff_right (useNontrivial : Bool) (x y : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      -(pilotEvalSelect useNontrivial x) = pilotEvalSelect useNontrivial y := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      -(pilotEvalWith (surrealSemantics useNontrivial) x) =
        pilotEvalWith (surrealSemantics useNontrivial) y
  exact pilotEvalWith_add_normalize_eq_zero_iff_right (surrealSemantics useNontrivial) x y

theorem pilotEvalSelect_add_normalize_left_eq_zero_iff
    (useNontrivial : Bool) (x y : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) = 0 ↔
      pilotEvalSelect useNontrivial y = -(pilotEvalSelect useNontrivial x) := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) = 0 ↔
      pilotEvalWith (surrealSemantics useNontrivial) y =
        -(pilotEvalWith (surrealSemantics useNontrivial) x)
  exact pilotEvalWith_add_normalize_left_eq_zero_iff (surrealSemantics useNontrivial) x y

theorem pilotEvalSelect_add_normalize_left_eq_zero_iff_left
    (useNontrivial : Bool) (x y : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) = 0 ↔
      pilotEvalSelect useNontrivial x = -(pilotEvalSelect useNontrivial y) := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) = 0 ↔
      pilotEvalWith (surrealSemantics useNontrivial) x =
        -(pilotEvalWith (surrealSemantics useNontrivial) y)
  exact pilotEvalWith_add_normalize_left_eq_zero_iff_left (surrealSemantics useNontrivial) x y

theorem pilotEvalSelect_add_normalize_left_eq_zero_iff_right
    (useNontrivial : Bool) (x y : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) = 0 ↔
      -(pilotEvalSelect useNontrivial x) = pilotEvalSelect useNontrivial y := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) = 0 ↔
      -(pilotEvalWith (surrealSemantics useNontrivial) x) =
        pilotEvalWith (surrealSemantics useNontrivial) y
  exact pilotEvalWith_add_normalize_left_eq_zero_iff_right (surrealSemantics useNontrivial) x y

theorem pilotEvalSelect_add_normalize_right_eq_zero_iff
    (useNontrivial : Bool) (x y : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEvalSelect useNontrivial y = -(pilotEvalSelect useNontrivial x) := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEvalWith (surrealSemantics useNontrivial) y =
        -(pilotEvalWith (surrealSemantics useNontrivial) x)
  exact pilotEvalWith_add_normalize_right_eq_zero_iff (surrealSemantics useNontrivial) x y

theorem pilotEvalSelect_add_normalize_right_eq_zero_iff_left
    (useNontrivial : Bool) (x y : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEvalSelect useNontrivial x = -(pilotEvalSelect useNontrivial y) := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEvalWith (surrealSemantics useNontrivial) x =
        -(pilotEvalWith (surrealSemantics useNontrivial) y)
  exact pilotEvalWith_add_normalize_right_eq_zero_iff_left (surrealSemantics useNontrivial) x y

theorem pilotEvalSelect_add_normalize_right_eq_zero_iff_right
    (useNontrivial : Bool) (x y : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      -(pilotEvalSelect useNontrivial x) = pilotEvalSelect useNontrivial y := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      -(pilotEvalWith (surrealSemantics useNontrivial) x) =
        pilotEvalWith (surrealSemantics useNontrivial) y
  exact pilotEvalWith_add_normalize_right_eq_zero_iff_right (surrealSemantics useNontrivial) x y

theorem pilotEvalSelect_add_normalize_left (useNontrivial : Bool) (x y : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) =
      pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add x y) := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) =
      pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add x y)
  simp [pilotEvalWith_add, pilotEvalWith_normalize]

theorem pilotEvalSelect_add_normalize_right (useNontrivial : Bool) (x y : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) =
      pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add x y) := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) =
      pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add x y)
  simp [pilotEvalWith_add, pilotEvalWith_normalize]

theorem pilotEvalSelect_add_normalize (useNontrivial : Bool) (x y : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) =
      pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add x y) := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) =
      pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add x y)
  simp [pilotEvalWith_add, pilotEvalWith_normalize]

theorem pilotEvalSelect_normalize_add (useNontrivial : Bool) (x y : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.normalize
          (HeytingLean.Numbers.Surreal.Hyperseries.add x y)) =
      pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add x y) := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.normalize
          (HeytingLean.Numbers.Surreal.Hyperseries.add x y)) =
      pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add x y)
  simp [pilotEvalWith_add, pilotEvalWith_normalize]

theorem pilotEvalSelect_add_normalize_assoc (useNontrivial : Bool) (x y z : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.normalize y) z)) =
      pilotEvalSelect useNontrivial x +
        pilotEvalSelect useNontrivial y +
        pilotEvalSelect useNontrivial z := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.normalize y) z)) =
      pilotEvalWith (surrealSemantics useNontrivial) x +
        pilotEvalWith (surrealSemantics useNontrivial) y +
        pilotEvalWith (surrealSemantics useNontrivial) z
  simp [pilotEvalWith_add, pilotEvalWith_normalize, add_assoc]

theorem pilotEvalSelect_add_normalize_cancel_left
    (useNontrivial : Bool) (x y z : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) =
      pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) z) ↔
        pilotEvalSelect useNontrivial y = pilotEvalSelect useNontrivial z := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) =
      pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) z) ↔
        pilotEvalWith (surrealSemantics useNontrivial) y =
          pilotEvalWith (surrealSemantics useNontrivial) z
  exact pilotEvalWith_add_cancel_left (surrealSemantics useNontrivial)
    (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y z

theorem pilotEvalSelect_add_normalize_cancel_right
    (useNontrivial : Bool) (x y z : PilotSeries) :
    pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          y (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)) =
      pilotEvalSelect useNontrivial
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          z (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)) ↔
        pilotEvalSelect useNontrivial y = pilotEvalSelect useNontrivial z := by
  change
    pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          y (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)) =
      pilotEvalWith (surrealSemantics useNontrivial)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          z (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)) ↔
        pilotEvalWith (surrealSemantics useNontrivial) y =
          pilotEvalWith (surrealSemantics useNontrivial) z
  exact pilotEvalWith_add_cancel_right (surrealSemantics useNontrivial)
    (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y z

theorem pilotEvalWith_add_normalize_left
    (S : SurrealExpLogSemantics) (x y : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) =
      pilotEvalWith S (HeytingLean.Numbers.Surreal.Hyperseries.add x y) := by
  simp [pilotEvalWith_add, pilotEvalWith_normalize]

theorem pilotEvalWith_add_normalize_right
    (S : SurrealExpLogSemantics) (x y : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) =
      pilotEvalWith S (HeytingLean.Numbers.Surreal.Hyperseries.add x y) := by
  simp [pilotEvalWith_add, pilotEvalWith_normalize]

theorem pilotEvalWith_add_normalize
    (S : SurrealExpLogSemantics) (x y : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) =
      pilotEvalWith S (HeytingLean.Numbers.Surreal.Hyperseries.add x y) := by
  simp [pilotEvalWith_add, pilotEvalWith_normalize]

theorem pilotEvalWith_normalize_add
    (S : SurrealExpLogSemantics) (x y : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.normalize
          (HeytingLean.Numbers.Surreal.Hyperseries.add x y)) =
      pilotEvalWith S (HeytingLean.Numbers.Surreal.Hyperseries.add x y) := by
  simp [pilotEvalWith_add, pilotEvalWith_normalize]

theorem pilotEvalWith_add_normalize_assoc
    (S : SurrealExpLogSemantics) (x y z : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.normalize y) z)) =
      pilotEvalWith S x + pilotEvalWith S y + pilotEvalWith S z := by
  simp [pilotEvalWith_add, pilotEvalWith_normalize, add_assoc]

theorem pilotEvalWith_add_normalize_cancel_left
    (S : SurrealExpLogSemantics) (x y z : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) =
      pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) z) ↔
        pilotEvalWith S y = pilotEvalWith S z := by
  exact pilotEvalWith_add_cancel_left S (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y z

theorem pilotEvalWith_add_normalize_cancel_right
    (S : SurrealExpLogSemantics) (x y z : PilotSeries) :
    pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          y (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)) =
      pilotEvalWith S
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          z (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)) ↔
        pilotEvalWith S y = pilotEvalWith S z := by
  exact pilotEvalWith_add_cancel_right S (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y z

theorem pilotEval_add_cancel_left (x y z : PilotSeries) :
    pilotEval (HeytingLean.Numbers.Surreal.Hyperseries.add x y) =
      pilotEval (HeytingLean.Numbers.Surreal.Hyperseries.add x z) ↔
        pilotEval y = pilotEval z := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_cancel_left surrealSemanticsDefault x y z)

theorem pilotEval_add_cancel_right (x y z : PilotSeries) :
    pilotEval (HeytingLean.Numbers.Surreal.Hyperseries.add y x) =
      pilotEval (HeytingLean.Numbers.Surreal.Hyperseries.add z x) ↔
        pilotEval y = pilotEval z := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_cancel_right surrealSemanticsDefault x y z)

theorem pilotEvalSelect_false_add_cancel_left (x y z : PilotSeries) :
    pilotEvalSelect false (HeytingLean.Numbers.Surreal.Hyperseries.add x y) =
      pilotEvalSelect false (HeytingLean.Numbers.Surreal.Hyperseries.add x z) ↔
        pilotEvalSelect false y = pilotEvalSelect false z := by
  change pilotEval (HeytingLean.Numbers.Surreal.Hyperseries.add x y) =
      pilotEval (HeytingLean.Numbers.Surreal.Hyperseries.add x z) ↔
        pilotEval y = pilotEval z
  exact pilotEval_add_cancel_left x y z

theorem pilotEvalSelect_false_add_cancel_right (x y z : PilotSeries) :
    pilotEvalSelect false (HeytingLean.Numbers.Surreal.Hyperseries.add y x) =
      pilotEvalSelect false (HeytingLean.Numbers.Surreal.Hyperseries.add z x) ↔
        pilotEvalSelect false y = pilotEvalSelect false z := by
  change pilotEval (HeytingLean.Numbers.Surreal.Hyperseries.add y x) =
      pilotEval (HeytingLean.Numbers.Surreal.Hyperseries.add z x) ↔
        pilotEval y = pilotEval z
  exact pilotEval_add_cancel_right x y z

theorem pilotEval_add_eq_zero_iff (x y : PilotSeries) :
    pilotEval (HeytingLean.Numbers.Surreal.Hyperseries.add x y) = 0 ↔
      pilotEval y = -(pilotEval x) := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_eq_zero_iff surrealSemanticsDefault x y)

theorem pilotEval_add_eq_zero_iff_left (x y : PilotSeries) :
    pilotEval (HeytingLean.Numbers.Surreal.Hyperseries.add x y) = 0 ↔
      pilotEval x = -(pilotEval y) := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_eq_zero_iff_left surrealSemanticsDefault x y)

theorem pilotEval_add_eq_zero_iff_right (x y : PilotSeries) :
    pilotEval (HeytingLean.Numbers.Surreal.Hyperseries.add x y) = 0 ↔
      -(pilotEval x) = pilotEval y := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_eq_zero_iff_right surrealSemanticsDefault x y)

theorem pilotEvalSelect_false_add_eq_zero_iff (x y : PilotSeries) :
    pilotEvalSelect false (HeytingLean.Numbers.Surreal.Hyperseries.add x y) = 0 ↔
      pilotEvalSelect false y = -(pilotEvalSelect false x) := by
  change pilotEval (HeytingLean.Numbers.Surreal.Hyperseries.add x y) = 0 ↔
      pilotEval y = -(pilotEval x)
  exact pilotEval_add_eq_zero_iff x y

theorem pilotEvalSelect_false_add_eq_zero_iff_left (x y : PilotSeries) :
    pilotEvalSelect false (HeytingLean.Numbers.Surreal.Hyperseries.add x y) = 0 ↔
      pilotEvalSelect false x = -(pilotEvalSelect false y) := by
  change pilotEval (HeytingLean.Numbers.Surreal.Hyperseries.add x y) = 0 ↔
      pilotEval x = -(pilotEval y)
  exact pilotEval_add_eq_zero_iff_left x y

theorem pilotEvalSelect_false_add_eq_zero_iff_right (x y : PilotSeries) :
    pilotEvalSelect false (HeytingLean.Numbers.Surreal.Hyperseries.add x y) = 0 ↔
      -(pilotEvalSelect false x) = pilotEvalSelect false y := by
  change pilotEval (HeytingLean.Numbers.Surreal.Hyperseries.add x y) = 0 ↔
      -(pilotEval x) = pilotEval y
  exact pilotEval_add_eq_zero_iff_right x y

theorem pilotEval_add_normalize_left_eq_zero_iff (x y : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) = 0 ↔
      pilotEval y = -(pilotEval x) := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_normalize_left_eq_zero_iff surrealSemanticsDefault x y)

theorem pilotEval_add_normalize_left_eq_zero_iff_left (x y : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) = 0 ↔
      pilotEval x = -(pilotEval y) := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_normalize_left_eq_zero_iff_left surrealSemanticsDefault x y)

theorem pilotEval_add_normalize_left_eq_zero_iff_right (x y : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) = 0 ↔
      -(pilotEval x) = pilotEval y := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_normalize_left_eq_zero_iff_right surrealSemanticsDefault x y)

theorem pilotEvalSelect_false_add_normalize_left_eq_zero_iff (x y : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) = 0 ↔
      pilotEvalSelect false y = -(pilotEvalSelect false x) := by
  change pilotEval
      (HeytingLean.Numbers.Surreal.Hyperseries.add
        (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) = 0 ↔
      pilotEval y = -(pilotEval x)
  exact pilotEval_add_normalize_left_eq_zero_iff x y

theorem pilotEvalSelect_false_add_normalize_left_eq_zero_iff_left (x y : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) = 0 ↔
      pilotEvalSelect false x = -(pilotEvalSelect false y) := by
  change pilotEval
      (HeytingLean.Numbers.Surreal.Hyperseries.add
        (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) = 0 ↔
      pilotEval x = -(pilotEval y)
  exact pilotEval_add_normalize_left_eq_zero_iff_left x y

theorem pilotEvalSelect_false_add_normalize_left_eq_zero_iff_right (x y : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) = 0 ↔
      -(pilotEvalSelect false x) = pilotEvalSelect false y := by
  change pilotEval
      (HeytingLean.Numbers.Surreal.Hyperseries.add
        (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) = 0 ↔
      -(pilotEval x) = pilotEval y
  exact pilotEval_add_normalize_left_eq_zero_iff_right x y

theorem pilotEval_add_normalize_right_eq_zero_iff (x y : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEval y = -(pilotEval x) := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_normalize_right_eq_zero_iff surrealSemanticsDefault x y)

theorem pilotEval_add_normalize_right_eq_zero_iff_left (x y : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEval x = -(pilotEval y) := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_normalize_right_eq_zero_iff_left surrealSemanticsDefault x y)

theorem pilotEval_add_normalize_right_eq_zero_iff_right (x y : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      -(pilotEval x) = pilotEval y := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_normalize_right_eq_zero_iff_right surrealSemanticsDefault x y)

theorem pilotEvalSelect_false_add_normalize_right_eq_zero_iff (x y : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEvalSelect false y = -(pilotEvalSelect false x) := by
  change pilotEval
      (HeytingLean.Numbers.Surreal.Hyperseries.add
        x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEval y = -(pilotEval x)
  exact pilotEval_add_normalize_right_eq_zero_iff x y

theorem pilotEvalSelect_false_add_normalize_right_eq_zero_iff_left (x y : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEvalSelect false x = -(pilotEvalSelect false y) := by
  change pilotEval
      (HeytingLean.Numbers.Surreal.Hyperseries.add
        x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEval x = -(pilotEval y)
  exact pilotEval_add_normalize_right_eq_zero_iff_left x y

theorem pilotEvalSelect_false_add_normalize_right_eq_zero_iff_right (x y : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      -(pilotEvalSelect false x) = pilotEvalSelect false y := by
  change pilotEval
      (HeytingLean.Numbers.Surreal.Hyperseries.add
        x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      -(pilotEval x) = pilotEval y
  exact pilotEval_add_normalize_right_eq_zero_iff_right x y

theorem pilotEval_add_normalize_eq_zero_iff (x y : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEval y = -(pilotEval x) := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_normalize_eq_zero_iff surrealSemanticsDefault x y)

theorem pilotEval_add_normalize_eq_zero_iff_left (x y : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEval x = -(pilotEval y) := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_normalize_eq_zero_iff_left surrealSemanticsDefault x y)

theorem pilotEval_add_normalize_eq_zero_iff_right (x y : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      -(pilotEval x) = pilotEval y := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_normalize_eq_zero_iff_right surrealSemanticsDefault x y)

theorem pilotEvalSelect_false_add_normalize_eq_zero_iff (x y : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEvalSelect false y = -(pilotEvalSelect false x) := by
  change pilotEval
      (HeytingLean.Numbers.Surreal.Hyperseries.add
        (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
        (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEval y = -(pilotEval x)
  exact pilotEval_add_normalize_eq_zero_iff x y

theorem pilotEvalSelect_false_add_normalize_eq_zero_iff_left (x y : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEvalSelect false x = -(pilotEvalSelect false y) := by
  change pilotEval
      (HeytingLean.Numbers.Surreal.Hyperseries.add
        (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
        (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEval x = -(pilotEval y)
  exact pilotEval_add_normalize_eq_zero_iff_left x y

theorem pilotEvalSelect_false_add_normalize_eq_zero_iff_right (x y : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      -(pilotEvalSelect false x) = pilotEvalSelect false y := by
  change pilotEval
      (HeytingLean.Numbers.Surreal.Hyperseries.add
        (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
        (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      -(pilotEval x) = pilotEval y
  exact pilotEval_add_normalize_eq_zero_iff_right x y

theorem pilotEval_add_normalize_left (x y : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) =
      pilotEval (HeytingLean.Numbers.Surreal.Hyperseries.add x y) := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_normalize_left surrealSemanticsDefault x y)

theorem pilotEval_add_normalize_right (x y : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) =
      pilotEval (HeytingLean.Numbers.Surreal.Hyperseries.add x y) := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_normalize_right surrealSemanticsDefault x y)

theorem pilotEvalSelect_false_add_normalize_left (x y : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) =
      pilotEvalSelect false (HeytingLean.Numbers.Surreal.Hyperseries.add x y) := by
  change pilotEval
      (HeytingLean.Numbers.Surreal.Hyperseries.add
        (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) =
      pilotEval (HeytingLean.Numbers.Surreal.Hyperseries.add x y)
  exact pilotEval_add_normalize_left x y

theorem pilotEvalSelect_false_add_normalize_right (x y : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) =
      pilotEvalSelect false (HeytingLean.Numbers.Surreal.Hyperseries.add x y) := by
  change pilotEval
      (HeytingLean.Numbers.Surreal.Hyperseries.add
        x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) =
      pilotEval (HeytingLean.Numbers.Surreal.Hyperseries.add x y)
  exact pilotEval_add_normalize_right x y

theorem pilotEval_add_normalize (x y : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) =
      pilotEval (HeytingLean.Numbers.Surreal.Hyperseries.add x y) := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_normalize surrealSemanticsDefault x y)

theorem pilotEvalSelect_false_add_normalize (x y : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) =
      pilotEvalSelect false (HeytingLean.Numbers.Surreal.Hyperseries.add x y) := by
  change pilotEval
      (HeytingLean.Numbers.Surreal.Hyperseries.add
        (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
        (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) =
      pilotEval (HeytingLean.Numbers.Surreal.Hyperseries.add x y)
  exact pilotEval_add_normalize x y

theorem pilotEval_normalize_add (x y : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.normalize
          (HeytingLean.Numbers.Surreal.Hyperseries.add x y)) =
      pilotEval (HeytingLean.Numbers.Surreal.Hyperseries.add x y) := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_normalize_add surrealSemanticsDefault x y)

theorem pilotEvalSelect_false_normalize_add (x y : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.normalize
          (HeytingLean.Numbers.Surreal.Hyperseries.add x y)) =
      pilotEvalSelect false (HeytingLean.Numbers.Surreal.Hyperseries.add x y) := by
  change pilotEval
      (HeytingLean.Numbers.Surreal.Hyperseries.normalize
        (HeytingLean.Numbers.Surreal.Hyperseries.add x y)) =
      pilotEval (HeytingLean.Numbers.Surreal.Hyperseries.add x y)
  exact pilotEval_normalize_add x y

theorem pilotEval_add_normalize_assoc (x y z : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.normalize y) z)) =
      pilotEval x + pilotEval y + pilotEval z := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_normalize_assoc surrealSemanticsDefault x y z)

theorem pilotEvalSelect_false_add_normalize_assoc (x y z : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.normalize y) z)) =
      pilotEvalSelect false x +
        pilotEvalSelect false y +
        pilotEvalSelect false z := by
  change pilotEval
      (HeytingLean.Numbers.Surreal.Hyperseries.add
        (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y) z)) =
      pilotEval x + pilotEval y + pilotEval z
  exact pilotEval_add_normalize_assoc x y z

theorem pilotEval_add_normalize_cancel_left (x y z : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) =
      pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) z) ↔
        pilotEval y = pilotEval z := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_normalize_cancel_left surrealSemanticsDefault x y z)

theorem pilotEval_add_normalize_cancel_right (x y z : PilotSeries) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          y (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)) =
      pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          z (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)) ↔
        pilotEval y = pilotEval z := by
  simpa [pilotEval, pilotEvalWith, ofPilotSeries] using
    (pilotEvalWith_add_normalize_cancel_right surrealSemanticsDefault x y z)

theorem pilotEvalSelect_false_add_normalize_cancel_left (x y z : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) =
      pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) z) ↔
        pilotEvalSelect false y = pilotEvalSelect false z := by
  change pilotEval
      (HeytingLean.Numbers.Surreal.Hyperseries.add
        (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) =
      pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) z) ↔
        pilotEval y = pilotEval z
  exact pilotEval_add_normalize_cancel_left x y z

theorem pilotEvalSelect_false_add_normalize_cancel_right (x y z : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          y (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)) =
      pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          z (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)) ↔
        pilotEvalSelect false y = pilotEvalSelect false z := by
  change pilotEval
      (HeytingLean.Numbers.Surreal.Hyperseries.add
        y (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)) =
      pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          z (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)) ↔
        pilotEval y = pilotEval z
  exact pilotEval_add_normalize_cancel_right x y z

end PilotBridge

end SurrealSpecialization

end Hyperseries
end HeytingLean
