import HeytingLean.Hyperseries.Equivalence

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Hyperseries

noncomputable section

abbrev SnegFullWiring : SurrealExpLogSemantics := SurrealExpLogSemantics.negSemantics

example [HyperserialDescription Surreal] (e : HExpr) :
    describeExpr e = describeExprWith surrealSemanticsDefault e := by
  rfl

example [HyperserialDescription Surreal] (s : PilotSeries) :
    ofPilotSeries s = ofPilotSeriesWith surrealSemanticsDefault s := by
  rfl

example [HyperserialDescription Surreal] (s : PilotSeries) :
    evalOmega (ofPilotSeries s) = evalOmega (ofPilotSeriesWith surrealSemanticsDefault s) := by
  rfl

example : SurrealExpLogSemantics.Nontrivial SnegFullWiring := by
  simpa [SnegFullWiring] using SurrealExpLogSemantics.nontrivial_negSemantics

example [HyperserialDescription Surreal] (e : HExpr) :
    evalOmega (describeExprWith SnegFullWiring e) =
      HExpr.eval (SurrealExpLogSemantics.toModel SnegFullWiring) e := by
  simp [SnegFullWiring, evalOmega_describeExprWith]

example [HyperserialDescription Surreal] (s : PilotSeries) :
    evalOmega (ofPilotSeriesWith SnegFullWiring s) =
      HExpr.eval (SurrealExpLogSemantics.toModel SnegFullWiring) (BridgePilot.ofSeries.{0} s) := by
  simpa [SnegFullWiring] using evalOmega_ofPilotSeriesWith SnegFullWiring s

example (x : Surreal) : (surrealModelWith false).exp x = x := by
  simp [surrealModelWith, surrealSemantics]

example [HyperserialDescription Surreal] (e : HExpr) :
    evalOmega (describeExprWith (surrealSemantics true) e) = HExpr.eval (surrealModelWith true) e := by
  simp [surrealModelWith, surrealSemantics]

example [HyperserialDescription Surreal] (e : HExpr) :
    describeExprSelect false e = describeExpr e := by
  simpa using describeExprSelect_false e

example [HyperserialDescription Surreal] (e : HExpr) :
    evalOmega (describeExprSelect true e) = HExpr.eval (surrealModelWith true) e := by
  exact evalOmega_describeExprSelect true e

example [HyperserialDescription Surreal] (s : PilotSeries) :
    ofPilotSeriesSelect false s = ofPilotSeries s := by
  simpa using ofPilotSeriesSelect_false s

example [HyperserialDescription Surreal] (s : PilotSeries) :
    evalOmega (ofPilotSeriesSelect true s) =
      HExpr.eval (surrealModelWith true) (BridgePilot.ofSeries.{0} s) := by
  simpa using evalOmega_ofPilotSeriesSelect true s

example [HyperserialDescription Surreal] (s : PilotSeries) :
    pilotEvalSelect true s = evalOmega (ofPilotSeriesSelect true s) := by
  rfl

example [HyperserialDescription Surreal] :
    pilotEvalSelect true ([] : PilotSeries) = 0 := by
  exact pilotEvalSelect_nil true

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect true (x ++ y) = pilotEvalSelect true x + pilotEvalSelect true y := by
  exact pilotEvalSelect_append true x y

example [HyperserialDescription Surreal] (x y z : PilotSeries) :
    pilotEvalSelect true ((x ++ y) ++ z) =
      pilotEvalSelect true x + pilotEvalSelect true y + pilotEvalSelect true z := by
  exact pilotEvalSelect_append_assoc true x y z

example [HyperserialDescription Surreal] (x y z : PilotSeries) :
    pilotEvalSelect false ((x ++ y) ++ z) =
      pilotEvalSelect false x + pilotEvalSelect false y + pilotEvalSelect false z := by
  exact pilotEvalSelect_false_append_assoc x y z

example [HyperserialDescription Surreal] (x y z : PilotSeries) :
    pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.add x y) z) =
      pilotEvalSelect true x + pilotEvalSelect true y + pilotEvalSelect true z := by
  exact pilotEvalSelect_add_assoc true x y z

example [HyperserialDescription Surreal] (x y z : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.add x y) z) =
      pilotEvalSelect false x + pilotEvalSelect false y + pilotEvalSelect false z := by
  exact pilotEvalSelect_false_add_assoc x y z

example [HyperserialDescription Surreal] (x y z : PilotSeries) :
    pilotEvalWith (surrealSemantics true)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.add x y) z) =
      pilotEvalWith (surrealSemantics true) x +
        pilotEvalWith (surrealSemantics true) y +
        pilotEvalWith (surrealSemantics true) z := by
  exact pilotEvalWith_add_assoc (surrealSemantics true) x y z

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect true (HeytingLean.Numbers.Surreal.Hyperseries.add x y) =
      pilotEvalSelect true (HeytingLean.Numbers.Surreal.Hyperseries.add y x) := by
  exact pilotEvalSelect_add_comm true x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect false (HeytingLean.Numbers.Surreal.Hyperseries.add x y) =
      pilotEvalSelect false (HeytingLean.Numbers.Surreal.Hyperseries.add y x) := by
  exact pilotEvalSelect_false_add_comm x y

example [HyperserialDescription Surreal] (s : PilotSeries) :
    pilotEvalSelect true (HeytingLean.Numbers.Surreal.Hyperseries.normalize s) =
      pilotEvalSelect true s := by
  exact pilotEvalSelect_normalize true s

example [HyperserialDescription Surreal] (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂)) = 0 := by
  exact pilotEvalSelect_mul_monomial_zero_left true c e₁ e₂

example [HyperserialDescription Surreal] (c₁ c₂ : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF)
    (hcoeff : c₁ * c₂ = 0) :
    pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₁ e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₂ e₂)) = 0 := by
  exact pilotEvalSelect_mul_monomial_eq_zero_of_coeff_mul_eq_zero true c₁ c₂ e₁ e₂ hcoeff

example [HyperserialDescription Surreal] (c₁ c₂ : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₁ e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₂ e₂)) =
      pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.monomial (c₁ * c₂) (e₁ + e₂)) := by
  exact pilotEvalSelect_false_mul_monomial c₁ c₂ e₁ e₂

example [HyperserialDescription Surreal] (c₁ c₂ : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF)
    (hcoeff : c₁ * c₂ = 0) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₁ e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₂ e₂)) = 0 := by
  exact pilotEvalSelect_false_mul_monomial_eq_zero_of_coeff_mul_eq_zero c₁ c₂ e₁ e₂ hcoeff

example [HyperserialDescription Surreal] (c₁ c₂ : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₁ e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₂ e₂)) = 0 ↔
      pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.monomial (c₁ * c₂) (e₁ + e₂)) = 0 := by
  exact pilotEvalSelect_mul_monomial_eq_zero_iff true c₁ c₂ e₁ e₂

example [HyperserialDescription Surreal] (c₁ c₂ : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.mul
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₁ e₁)
          (HeytingLean.Numbers.Surreal.Hyperseries.monomial c₂ e₂)) = 0 ↔
      pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.monomial (c₁ * c₂) (e₁ + e₂)) = 0 := by
  exact pilotEvalSelect_false_mul_monomial_eq_zero_iff c₁ c₂ e₁ e₂

example [HyperserialDescription Surreal] (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) = pilotEvalSelect true s := by
  exact pilotEvalSelect_add_mul_monomial_zero_left_lhs true c e₁ e₂ s

example [HyperserialDescription Surreal] (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) = 0 ↔
      pilotEvalSelect true s = 0 := by
  exact pilotEvalSelect_add_mul_monomial_zero_right_rhs_eq_zero_iff true s c e₁ e₂

example [HyperserialDescription Surreal] (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) = 0 ↔
      0 = pilotEvalSelect true s := by
  exact pilotEvalSelect_add_mul_monomial_zero_right_rhs_eq_zero_iff_right true s c e₁ e₂

example [HyperserialDescription Surreal] (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) = 0 ↔
      0 = pilotEvalSelect true s := by
  exact pilotEvalSelect_add_mul_monomial_zero_left_lhs_eq_zero_iff_right true c e₁ e₂ s

example [HyperserialDescription Surreal] (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) = 0 ↔
      0 = pilotEvalSelect true s := by
  exact pilotEvalSelect_add_mul_monomial_zero_right_lhs_eq_zero_iff_right true c e₁ e₂ s

example [HyperserialDescription Surreal] (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) = 0 ↔
      0 = pilotEvalSelect true s := by
  exact pilotEvalSelect_add_mul_monomial_zero_left_rhs_eq_zero_iff_right true s c e₁ e₂

example [HyperserialDescription Surreal] (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    0 =
      pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) ↔
      0 = pilotEvalSelect true s := by
  exact pilotEvalSelect_add_mul_monomial_zero_right_rhs_eq_zero_iff_left true s c e₁ e₂

example [HyperserialDescription Surreal] (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    0 =
      pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) ↔
      0 = pilotEvalSelect true s := by
  exact pilotEvalSelect_add_mul_monomial_zero_left_lhs_eq_zero_iff_left true c e₁ e₂ s

example [HyperserialDescription Surreal] (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    0 =
      pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) ↔
      0 = pilotEvalSelect true s := by
  exact pilotEvalSelect_add_mul_monomial_zero_right_lhs_eq_zero_iff_left true c e₁ e₂ s

example [HyperserialDescription Surreal] (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    0 =
      pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) ↔
      0 = pilotEvalSelect true s := by
  exact pilotEvalSelect_add_mul_monomial_zero_left_rhs_eq_zero_iff_left true s c e₁ e₂

example [HyperserialDescription Surreal] (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) = 0 ↔
      0 = pilotEval s := by
  exact pilotEval_add_mul_monomial_zero_right_rhs_eq_zero_iff_right s c e₁ e₂

example [HyperserialDescription Surreal] (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    0 =
      pilotEval
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) ↔
      0 = pilotEval s := by
  exact pilotEval_add_mul_monomial_zero_left_lhs_eq_zero_iff_left c e₁ e₂ s

example [HyperserialDescription Surreal] (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    0 =
      pilotEvalWith (surrealSemantics true)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) ↔
      0 = pilotEvalWith (surrealSemantics true) s := by
  exact pilotEvalWith_add_mul_monomial_zero_right_rhs_eq_zero_iff_left (surrealSemantics true) s c e₁ e₂

example [HyperserialDescription Surreal] (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalWith (surrealSemantics true)
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) =
      pilotEvalWith (surrealSemantics true) t ↔
      pilotEvalWith (surrealSemantics true) t = pilotEvalWith (surrealSemantics true) s := by
  exact pilotEvalWith_add_mul_monomial_zero_right_lhs_eq_iff_right (surrealSemantics true) c e₁ e₂ s t

example [HyperserialDescription Surreal] (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) =
      pilotEvalSelect true t ↔
      pilotEvalSelect true s = pilotEvalSelect true t := by
  exact pilotEvalSelect_add_mul_monomial_zero_right_lhs_eq_iff true c e₁ e₂ s t

example [HyperserialDescription Surreal] (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) =
      pilotEvalSelect true t ↔
      pilotEvalSelect true t = pilotEvalSelect true s := by
  exact pilotEvalSelect_add_mul_monomial_zero_left_lhs_eq_iff_right true c e₁ e₂ s t

example [HyperserialDescription Surreal] (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) =
      pilotEvalSelect true t ↔
      pilotEvalSelect true t = pilotEvalSelect true s := by
  exact pilotEvalSelect_add_mul_monomial_zero_right_lhs_eq_iff_right true c e₁ e₂ s t

example [HyperserialDescription Surreal] (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) =
      pilotEvalSelect true t ↔
      pilotEvalSelect true t = pilotEvalSelect true s := by
  exact pilotEvalSelect_add_mul_monomial_zero_left_rhs_eq_iff_right true s t c e₁ e₂

example [HyperserialDescription Surreal] (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) =
      pilotEvalSelect true t ↔
      pilotEvalSelect true t = pilotEvalSelect true s := by
  exact pilotEvalSelect_add_mul_monomial_zero_right_rhs_eq_iff_right true s t c e₁ e₂

example [HyperserialDescription Surreal] (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalSelect true t =
      pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))
          s) ↔
      pilotEvalSelect true t = pilotEvalSelect true s := by
  exact pilotEvalSelect_add_mul_monomial_zero_right_lhs_eq_iff_left true c e₁ e₂ s t

example [HyperserialDescription Surreal] (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalSelect true t =
      pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) ↔
      pilotEvalSelect true t = pilotEvalSelect true s := by
  exact pilotEvalSelect_add_mul_monomial_zero_left_lhs_eq_iff_left true c e₁ e₂ s t

example [HyperserialDescription Surreal] (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect true t =
      pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))) ↔
      pilotEvalSelect true t = pilotEvalSelect true s := by
  exact pilotEvalSelect_add_mul_monomial_zero_left_rhs_eq_iff_left true s t c e₁ e₂

example [HyperserialDescription Surreal] (s t : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect true t =
      pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) ↔
      pilotEvalSelect true t = pilotEvalSelect true s := by
  exact pilotEvalSelect_add_mul_monomial_zero_right_rhs_eq_iff_left true s t c e₁ e₂

example [HyperserialDescription Surreal] (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) =
      pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          t
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) ↔
      pilotEvalSelect true s = pilotEvalSelect true t := by
  exact pilotEvalSelect_add_mul_monomial_zero_right_rhs_cancel true c e₁ e₂ s t

example [HyperserialDescription Surreal] (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) = pilotEvalSelect false s := by
  exact pilotEvalSelect_false_add_mul_monomial_zero_left_lhs c e₁ e₂ s

example [HyperserialDescription Surreal] (s : PilotSeries) (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) = 0 ↔
      pilotEvalSelect false s = 0 := by
  exact pilotEvalSelect_false_add_mul_monomial_zero_right_rhs_eq_zero_iff s c e₁ e₂

example [HyperserialDescription Surreal] (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₂))
          s) =
      pilotEvalSelect false t ↔
      pilotEvalSelect false s = pilotEvalSelect false t := by
  exact pilotEvalSelect_false_add_mul_monomial_zero_left_lhs_eq_iff c e₁ e₂ s t

example [HyperserialDescription Surreal] (s : PilotSeries) (c : Int)
    (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) = 0 ↔
      0 = pilotEvalSelect false s := by
  exact pilotEvalSelect_false_add_mul_monomial_zero_right_rhs_eq_zero_iff_right s c e₁ e₂

example [HyperserialDescription Surreal] (s : PilotSeries) (c : Int)
    (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    0 =
      pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) ↔
      0 = pilotEvalSelect false s := by
  exact pilotEvalSelect_false_add_mul_monomial_zero_right_rhs_eq_zero_iff_left s c e₁ e₂

example [HyperserialDescription Surreal] (s t : PilotSeries) (c : Int)
    (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) =
      pilotEvalSelect false t ↔
      pilotEvalSelect false t = pilotEvalSelect false s := by
  exact pilotEvalSelect_false_add_mul_monomial_zero_right_rhs_eq_iff_right s t c e₁ e₂

example [HyperserialDescription Surreal] (s t : PilotSeries) (c : Int)
    (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) :
    pilotEvalSelect false t =
      pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          s
          (HeytingLean.Numbers.Surreal.Hyperseries.mul
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial c e₁)
            (HeytingLean.Numbers.Surreal.Hyperseries.monomial 0 e₂))) ↔
      pilotEvalSelect false t = pilotEvalSelect false s := by
  exact pilotEvalSelect_false_add_mul_monomial_zero_right_rhs_eq_iff_left s t c e₁ e₂

example [HyperserialDescription Surreal] (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) (s t : PilotSeries) :
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
  exact pilotEvalSelect_false_add_mul_monomial_zero_right_rhs_cancel c e₁ e₂ s t

example [HyperserialDescription Surreal] (c : Int) (e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF)
    (s t : PilotSeries) : True := by
  have _ := pilotEvalSelect_false_add_mul_monomial_zero_right_lhs c e₁ e₂ s
  have _ := pilotEvalSelect_false_add_mul_monomial_zero_left_rhs s c e₁ e₂
  have _ := pilotEvalSelect_false_add_mul_monomial_zero_right_rhs s c e₁ e₂
  have _ := pilotEvalSelect_false_add_mul_monomial_zero_left_lhs_eq_zero_iff c e₁ e₂ s
  have _ := pilotEvalSelect_false_add_mul_monomial_zero_right_lhs_eq_zero_iff c e₁ e₂ s
  have _ := pilotEvalSelect_false_add_mul_monomial_zero_left_rhs_eq_zero_iff s c e₁ e₂
  have _ := pilotEvalSelect_false_add_mul_monomial_zero_left_lhs_eq_zero_iff_right c e₁ e₂ s
  have _ := pilotEvalSelect_false_add_mul_monomial_zero_right_lhs_eq_zero_iff_right c e₁ e₂ s
  have _ := pilotEvalSelect_false_add_mul_monomial_zero_left_rhs_eq_zero_iff_right s c e₁ e₂
  have _ := pilotEvalSelect_false_add_mul_monomial_zero_left_lhs_eq_zero_iff_left c e₁ e₂ s
  have _ := pilotEvalSelect_false_add_mul_monomial_zero_right_lhs_eq_zero_iff_left c e₁ e₂ s
  have _ := pilotEvalSelect_false_add_mul_monomial_zero_left_rhs_eq_zero_iff_left s c e₁ e₂
  have _ := pilotEvalSelect_false_add_mul_monomial_zero_right_lhs_eq_iff c e₁ e₂ s t
  have _ := pilotEvalSelect_false_add_mul_monomial_zero_left_rhs_eq_iff s t c e₁ e₂
  have _ := pilotEvalSelect_false_add_mul_monomial_zero_right_rhs_eq_iff s t c e₁ e₂
  have _ := pilotEvalSelect_false_add_mul_monomial_zero_left_lhs_eq_iff_right c e₁ e₂ s t
  have _ := pilotEvalSelect_false_add_mul_monomial_zero_right_lhs_eq_iff_right c e₁ e₂ s t
  have _ := pilotEvalSelect_false_add_mul_monomial_zero_left_rhs_eq_iff_right s t c e₁ e₂
  have _ := pilotEvalSelect_false_add_mul_monomial_zero_left_lhs_eq_iff_left c e₁ e₂ s t
  have _ := pilotEvalSelect_false_add_mul_monomial_zero_right_lhs_eq_iff_left c e₁ e₂ s t
  have _ := pilotEvalSelect_false_add_mul_monomial_zero_left_rhs_eq_iff_left s t c e₁ e₂
  have _ := pilotEvalSelect_false_add_mul_monomial_zero_left_lhs_cancel c e₁ e₂ s t
  have _ := pilotEvalSelect_false_add_mul_monomial_zero_right_lhs_cancel c e₁ e₂ s t
  have _ := pilotEvalSelect_false_add_mul_monomial_zero_left_rhs_cancel c e₁ e₂ s t
  trivial

example [HyperserialDescription Surreal] (b : Bool) (x y z s t : PilotSeries)
    (c c₁ c₂ : Int) (e e₁ e₂ : HeytingLean.Numbers.Ordinal.OrdinalCNF) : True := by
  have _ := pilotEvalSelect_false s
  have _ := pilotEvalSelect_add b x y
  have _ := pilotEvalSelect_add_eq_zero_iff_left b x y
  have _ := pilotEvalSelect_monomial_zero b e
  have _ := pilotEvalSelect_monomial b c e
  have _ := pilotEvalSelect_mul_monomial b c₁ c₂ e₁ e₂
  have _ := pilotEvalSelect_mul_monomial_zero_right b c e₁ e₂
  have _ := pilotEvalSelect_add_mul_monomial_zero_right_lhs b c e₁ e₂ s
  have _ := pilotEvalSelect_add_mul_monomial_zero_left_rhs b s c e₁ e₂
  have _ := pilotEvalSelect_add_mul_monomial_zero_right_rhs b s c e₁ e₂
  have _ := pilotEvalSelect_add_mul_monomial_zero_left_lhs_eq_zero_iff b c e₁ e₂ s
  have _ := pilotEvalSelect_add_mul_monomial_zero_right_lhs_eq_zero_iff b c e₁ e₂ s
  have _ := pilotEvalSelect_add_mul_monomial_zero_left_rhs_eq_zero_iff b s c e₁ e₂
  have _ := pilotEvalSelect_add_mul_monomial_zero_left_lhs_eq_iff b c e₁ e₂ s t
  have _ := pilotEvalSelect_add_mul_monomial_zero_left_rhs_eq_iff b s t c e₁ e₂
  have _ := pilotEvalSelect_add_mul_monomial_zero_right_rhs_eq_iff b s t c e₁ e₂
  have _ := pilotEvalSelect_add_mul_monomial_zero_left_lhs_cancel b c e₁ e₂ s t
  have _ := pilotEvalSelect_add_mul_monomial_zero_right_lhs_cancel b c e₁ e₂ s t
  have _ := pilotEvalSelect_add_mul_monomial_zero_left_rhs_cancel b c e₁ e₂ s t
  have _ := pilotEvalSelect_add_normalize_right b x y
  have _ := pilotEvalSelect_add_normalize b x y
  have _ := pilotEvalSelect_normalize_add b x y
  have _ := pilotEvalSelect_add_normalize_eq_zero_iff b x y
  have _ := pilotEvalSelect_add_normalize_right_eq_zero_iff b x y
  have _ := pilotEvalSelect_add_normalize_left_eq_zero_iff_left b x y
  have _ := pilotEvalSelect_add_normalize_cancel_right b x y z
  trivial

example [HyperserialDescription Surreal] : True := by
  have _ := pilotEval_add
  have _ := pilotEval_add_assoc
  have _ := pilotEval_add_cancel_left
  have _ := pilotEval_add_cancel_right
  have _ := pilotEval_add_comm
  have _ := pilotEval_add_eq_zero_iff
  have _ := pilotEval_add_eq_zero_iff_left
  have _ := pilotEval_add_eq_zero_iff_right
  have _ := pilotEval_add_mul_monomial_zero_left_lhs
  have _ := pilotEval_add_mul_monomial_zero_left_lhs_cancel
  have _ := pilotEval_add_mul_monomial_zero_left_lhs_eq_iff
  have _ := pilotEval_add_mul_monomial_zero_left_lhs_eq_iff_left
  have _ := pilotEval_add_mul_monomial_zero_left_lhs_eq_iff_right
  have _ := pilotEval_add_mul_monomial_zero_left_lhs_eq_zero_iff
  have _ := pilotEval_add_mul_monomial_zero_left_lhs_eq_zero_iff_right
  have _ := pilotEval_add_mul_monomial_zero_left_rhs
  have _ := pilotEval_add_mul_monomial_zero_left_rhs_cancel
  have _ := pilotEval_add_mul_monomial_zero_left_rhs_eq_iff
  have _ := pilotEval_add_mul_monomial_zero_left_rhs_eq_iff_left
  have _ := pilotEval_add_mul_monomial_zero_left_rhs_eq_iff_right
  have _ := pilotEval_add_mul_monomial_zero_left_rhs_eq_zero_iff
  have _ := pilotEval_add_mul_monomial_zero_left_rhs_eq_zero_iff_left
  have _ := pilotEval_add_mul_monomial_zero_left_rhs_eq_zero_iff_right
  have _ := pilotEval_add_mul_monomial_zero_right_lhs
  have _ := pilotEval_add_mul_monomial_zero_right_lhs_cancel
  have _ := pilotEval_add_mul_monomial_zero_right_lhs_eq_iff
  have _ := pilotEval_add_mul_monomial_zero_right_lhs_eq_iff_left
  have _ := pilotEval_add_mul_monomial_zero_right_lhs_eq_iff_right
  have _ := pilotEval_add_mul_monomial_zero_right_lhs_eq_zero_iff
  have _ := pilotEval_add_mul_monomial_zero_right_lhs_eq_zero_iff_left
  have _ := pilotEval_add_mul_monomial_zero_right_lhs_eq_zero_iff_right
  have _ := pilotEval_add_mul_monomial_zero_right_rhs
  have _ := pilotEval_add_mul_monomial_zero_right_rhs_cancel
  have _ := pilotEval_add_mul_monomial_zero_right_rhs_eq_iff
  have _ := pilotEval_add_mul_monomial_zero_right_rhs_eq_iff_left
  have _ := pilotEval_add_mul_monomial_zero_right_rhs_eq_iff_right
  have _ := pilotEval_add_mul_monomial_zero_right_rhs_eq_zero_iff
  have _ := pilotEval_add_mul_monomial_zero_right_rhs_eq_zero_iff_left
  have _ := pilotEval_add_normalize
  have _ := pilotEval_add_normalize_assoc
  have _ := pilotEval_add_normalize_cancel_left
  have _ := pilotEval_add_normalize_cancel_right
  have _ := pilotEval_add_normalize_eq_zero_iff
  have _ := pilotEval_add_normalize_eq_zero_iff_left
  have _ := pilotEval_add_normalize_eq_zero_iff_right
  have _ := pilotEval_add_normalize_left
  have _ := pilotEval_add_normalize_left_eq_zero_iff
  have _ := pilotEval_add_normalize_left_eq_zero_iff_left
  have _ := pilotEval_add_normalize_left_eq_zero_iff_right
  have _ := pilotEval_add_normalize_right
  have _ := pilotEval_add_normalize_right_eq_zero_iff
  have _ := pilotEval_add_normalize_right_eq_zero_iff_left
  have _ := pilotEval_add_normalize_right_eq_zero_iff_right
  have _ := pilotEval_append
  have _ := pilotEval_append_assoc
  have _ := pilotEval_monomial
  have _ := pilotEval_monomial_zero
  have _ := pilotEval_mul_monomial
  have _ := pilotEval_mul_monomial_eq_zero_iff
  have _ := pilotEval_mul_monomial_eq_zero_of_coeff_mul_eq_zero
  have _ := pilotEval_mul_monomial_zero_left
  have _ := pilotEval_mul_monomial_zero_right
  have _ := pilotEval_nil
  have _ := pilotEval_normalize
  have _ := pilotEval_normalize_add
  trivial

example [HyperserialDescription Surreal] : True := by
  have _ := pilotEvalWith_add
  have _ := pilotEvalWith_add_cancel_left
  have _ := pilotEvalWith_add_cancel_right
  have _ := pilotEvalWith_add_comm
  have _ := pilotEvalWith_add_eq_zero_iff
  have _ := pilotEvalWith_add_eq_zero_iff_left
  have _ := pilotEvalWith_add_eq_zero_iff_right
  have _ := pilotEvalWith_add_mul_monomial_zero_left_lhs
  have _ := pilotEvalWith_add_mul_monomial_zero_left_lhs_cancel
  have _ := pilotEvalWith_add_mul_monomial_zero_left_lhs_eq_iff
  have _ := pilotEvalWith_add_mul_monomial_zero_left_lhs_eq_iff_left
  have _ := pilotEvalWith_add_mul_monomial_zero_left_lhs_eq_iff_right
  have _ := pilotEvalWith_add_mul_monomial_zero_left_lhs_eq_zero_iff
  have _ := pilotEvalWith_add_mul_monomial_zero_left_lhs_eq_zero_iff_left
  have _ := pilotEvalWith_add_mul_monomial_zero_left_lhs_eq_zero_iff_right
  have _ := pilotEvalWith_add_mul_monomial_zero_left_rhs
  have _ := pilotEvalWith_add_mul_monomial_zero_left_rhs_cancel
  have _ := pilotEvalWith_add_mul_monomial_zero_left_rhs_eq_iff
  have _ := pilotEvalWith_add_mul_monomial_zero_left_rhs_eq_iff_left
  have _ := pilotEvalWith_add_mul_monomial_zero_left_rhs_eq_iff_right
  have _ := pilotEvalWith_add_mul_monomial_zero_left_rhs_eq_zero_iff
  have _ := pilotEvalWith_add_mul_monomial_zero_left_rhs_eq_zero_iff_left
  have _ := pilotEvalWith_add_mul_monomial_zero_left_rhs_eq_zero_iff_right
  have _ := pilotEvalWith_add_mul_monomial_zero_right_lhs
  have _ := pilotEvalWith_add_mul_monomial_zero_right_lhs_cancel
  have _ := pilotEvalWith_add_mul_monomial_zero_right_lhs_eq_iff
  have _ := pilotEvalWith_add_mul_monomial_zero_right_lhs_eq_iff_left
  have _ := pilotEvalWith_add_mul_monomial_zero_right_lhs_eq_zero_iff
  have _ := pilotEvalWith_add_mul_monomial_zero_right_lhs_eq_zero_iff_left
  have _ := pilotEvalWith_add_mul_monomial_zero_right_lhs_eq_zero_iff_right
  have _ := pilotEvalWith_add_mul_monomial_zero_right_rhs
  have _ := pilotEvalWith_add_mul_monomial_zero_right_rhs_cancel
  have _ := pilotEvalWith_add_mul_monomial_zero_right_rhs_eq_iff
  have _ := pilotEvalWith_add_mul_monomial_zero_right_rhs_eq_iff_left
  have _ := pilotEvalWith_add_mul_monomial_zero_right_rhs_eq_iff_right
  have _ := pilotEvalWith_add_mul_monomial_zero_right_rhs_eq_zero_iff
  have _ := pilotEvalWith_add_mul_monomial_zero_right_rhs_eq_zero_iff_right
  have _ := pilotEvalWith_add_normalize
  have _ := pilotEvalWith_add_normalize_assoc
  have _ := pilotEvalWith_add_normalize_cancel_left
  have _ := pilotEvalWith_add_normalize_cancel_right
  have _ := pilotEvalWith_add_normalize_eq_zero_iff
  have _ := pilotEvalWith_add_normalize_eq_zero_iff_left
  have _ := pilotEvalWith_add_normalize_eq_zero_iff_right
  have _ := pilotEvalWith_add_normalize_left
  have _ := pilotEvalWith_add_normalize_left_eq_zero_iff
  have _ := pilotEvalWith_add_normalize_left_eq_zero_iff_left
  have _ := pilotEvalWith_add_normalize_left_eq_zero_iff_right
  have _ := pilotEvalWith_add_normalize_right
  have _ := pilotEvalWith_add_normalize_right_eq_zero_iff
  have _ := pilotEvalWith_add_normalize_right_eq_zero_iff_left
  have _ := pilotEvalWith_add_normalize_right_eq_zero_iff_right
  have _ := pilotEvalWith_append
  have _ := pilotEvalWith_append_assoc
  have _ := pilotEvalWith_monomial
  have _ := pilotEvalWith_monomial_zero
  have _ := pilotEvalWith_mul_monomial
  have _ := pilotEvalWith_mul_monomial_eq_zero_iff
  have _ := pilotEvalWith_mul_monomial_eq_zero_of_coeff_mul_eq_zero
  have _ := pilotEvalWith_mul_monomial_zero_left
  have _ := pilotEvalWith_mul_monomial_zero_right
  have _ := pilotEvalWith_nil
  have _ := pilotEvalWith_normalize
  have _ := pilotEvalWith_normalize_add
  trivial

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect true x = pilotEvalSelect true y ↔
      ofPilotSeriesSelect true x = ofPilotSeriesSelect true y := by
  exact pilotEvalSelect_eq_iff_ofPilotSeriesSelect_eq true x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect false x = pilotEvalSelect false y ↔
      ofPilotSeriesSelect false x = ofPilotSeriesSelect false y := by
  exact pilotEvalSelect_false_eq_iff_ofPilotSeriesSelect_eq x y

example [HyperserialDescription Surreal] (s : PilotSeries) :
    pilotEvalSelect false s = pilotEval s := by
  exact pilotEvalSelect_false_eq_pilotEval s

example [HyperserialDescription Surreal] (s : PilotSeries) :
    pilotEvalSelect false s = s.foldr (fun t acc => BridgePilot.termSem surrealModel t + acc) 0 := by
  exact pilotEvalSelect_false_eq_foldr s

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEval x = pilotEval y ↔
      ofPilotSeriesSelect false x = ofPilotSeriesSelect false y := by
  exact pilotEval_eq_iff_ofPilotSeriesSelect_false_eq x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect false x = pilotEvalSelect false y ↔
      ofPilotSeries x = ofPilotSeries y := by
  exact pilotEvalSelect_eq_iff_ofPilotSeries_eq x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect false x = pilotEvalSelect false y ↔
      ofPilotSeriesWith surrealSemanticsDefault x =
        ofPilotSeriesWith surrealSemanticsDefault y := by
  exact pilotEvalSelect_false_eq_iff_ofPilotSeriesWith_eq x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEval x = pilotEval y ↔
      ofPilotSeriesWith surrealSemanticsDefault x =
        ofPilotSeriesWith surrealSemanticsDefault y := by
  exact pilotEval_eq_iff_ofPilotSeriesWith_eq x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEval x = pilotEval y ↔ ofPilotSeries x = ofPilotSeries y := by
  exact pilotEval_eq_iff_ofPilotSeries_eq x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalWith (surrealSemantics true) x =
      pilotEvalWith (surrealSemantics true) y ↔
      ofPilotSeriesWith (surrealSemantics true) x =
        ofPilotSeriesWith (surrealSemantics true) y := by
  exact pilotEvalWith_eq_iff_ofPilotSeriesWith_eq (surrealSemantics true) x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect true x = pilotEvalSelect true y ↔
      ofPilotSeriesWith (surrealSemantics true) x = ofPilotSeriesWith (surrealSemantics true) y := by
  exact pilotEvalSelect_eq_iff_ofPilotSeriesWith_eq true x y

example [HyperserialDescription Surreal] (s : PilotSeries) :
    pilotEvalSelect false s = 0 ↔ ofPilotSeries s = 0 := by
  exact pilotEvalSelect_eq_zero_iff_ofPilotSeries_eq_zero s

example [HyperserialDescription Surreal] (s : PilotSeries) :
    pilotEvalSelect false s = 0 ↔
      ofPilotSeriesSelect false s = 0 := by
  exact pilotEvalSelect_false_eq_zero_iff_ofPilotSeriesSelect_eq_zero s

example [HyperserialDescription Surreal] (s : PilotSeries) :
    pilotEval s = 0 ↔ ofPilotSeriesSelect false s = 0 := by
  exact pilotEval_eq_zero_iff_ofPilotSeriesSelect_false_eq_zero s

example [HyperserialDescription Surreal] (s : PilotSeries) :
    pilotEvalSelect false s = 0 ↔ ofPilotSeriesWith surrealSemanticsDefault s = 0 := by
  exact pilotEvalSelect_false_eq_zero_iff_ofPilotSeriesWith_eq_zero s

example [HyperserialDescription Surreal] (s : PilotSeries) :
    pilotEval s = 0 ↔ ofPilotSeriesWith surrealSemanticsDefault s = 0 := by
  exact pilotEval_eq_zero_iff_ofPilotSeriesWith_eq_zero s

example [HyperserialDescription Surreal] (s : PilotSeries) :
    pilotEval s = evalOmega (ofPilotSeries s) := by
  exact pilotEval_eq_evalOmega_ofPilotSeries s

example [HyperserialDescription Surreal] (s : PilotSeries) :
    pilotEval s = 0 ↔ ofPilotSeries s = 0 := by
  exact pilotEval_eq_zero_iff_ofPilotSeries_eq_zero s

example [HyperserialDescription Surreal] (s : PilotSeries)
    (h : ofPilotSeries s = 0) : pilotEval s = 0 := by
  exact pilotEval_eq_zero_of_ofPilotSeries_eq_zero h

example [HyperserialDescription Surreal] (s : PilotSeries) :
    pilotEvalWith (surrealSemantics true) s = 0 ↔
      ofPilotSeriesWith (surrealSemantics true) s = 0 := by
  exact pilotEvalWith_eq_zero_iff_ofPilotSeriesWith_eq_zero (surrealSemantics true) s

example [HyperserialDescription Surreal] (s : PilotSeries) :
    pilotEval s = s.foldr (fun t acc => BridgePilot.termSem surrealModel t + acc) 0 := by
  exact pilotEval_eq_foldr s

example [HyperserialDescription Surreal] (s : PilotSeries) :
    pilotEvalWith (surrealSemantics true) s =
      s.foldr
        (fun t acc =>
          BridgePilot.termSem
            (SurrealExpLogSemantics.toModel (surrealSemantics true)) t + acc)
        0 := by
  exact pilotEvalWith_eq_foldr (surrealSemantics true) s

example [HyperserialDescription Surreal] (s : PilotSeries) :
    pilotEvalSelect true s = 0 ↔ ofPilotSeriesSelect true s = 0 := by
  exact pilotEvalSelect_eq_zero_iff_ofPilotSeriesSelect_eq_zero true s

example [HyperserialDescription Surreal] (s : PilotSeries) :
    pilotEvalSelect true s = 0 ↔
      ofPilotSeriesWith (surrealSemantics true) s = 0 := by
  exact pilotEvalSelect_eq_zero_iff_ofPilotSeriesWith_eq_zero true s

example [HyperserialDescription Surreal] (x y z : PilotSeries) :
    pilotEvalSelect true (HeytingLean.Numbers.Surreal.Hyperseries.add x y) =
      pilotEvalSelect true (HeytingLean.Numbers.Surreal.Hyperseries.add x z) ↔
        pilotEvalSelect true y = pilotEvalSelect true z := by
  exact pilotEvalSelect_add_cancel_left true x y z

example [HyperserialDescription Surreal] (x y z : PilotSeries) :
    pilotEvalSelect true (HeytingLean.Numbers.Surreal.Hyperseries.add y x) =
      pilotEvalSelect true (HeytingLean.Numbers.Surreal.Hyperseries.add z x) ↔
        pilotEvalSelect true y = pilotEvalSelect true z := by
  exact pilotEvalSelect_add_cancel_right true x y z

example [HyperserialDescription Surreal] (x y z : PilotSeries) :
    pilotEvalSelect false (HeytingLean.Numbers.Surreal.Hyperseries.add x y) =
      pilotEvalSelect false (HeytingLean.Numbers.Surreal.Hyperseries.add x z) ↔
        pilotEvalSelect false y = pilotEvalSelect false z := by
  exact pilotEvalSelect_false_add_cancel_left x y z

example [HyperserialDescription Surreal] (x y z : PilotSeries) :
    pilotEvalSelect false (HeytingLean.Numbers.Surreal.Hyperseries.add y x) =
      pilotEvalSelect false (HeytingLean.Numbers.Surreal.Hyperseries.add z x) ↔
        pilotEvalSelect false y = pilotEvalSelect false z := by
  exact pilotEvalSelect_false_add_cancel_right x y z

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect true (HeytingLean.Numbers.Surreal.Hyperseries.add x y) = 0 ↔
      pilotEvalSelect true y = -(pilotEvalSelect true x) := by
  exact pilotEvalSelect_add_eq_zero_iff true x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect false (HeytingLean.Numbers.Surreal.Hyperseries.add x y) = 0 ↔
      pilotEvalSelect false y = -(pilotEvalSelect false x) := by
  exact pilotEvalSelect_false_add_eq_zero_iff x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect true (HeytingLean.Numbers.Surreal.Hyperseries.add x y) = 0 ↔
      -(pilotEvalSelect true x) = pilotEvalSelect true y := by
  exact pilotEvalSelect_add_eq_zero_iff_right true x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect false (HeytingLean.Numbers.Surreal.Hyperseries.add x y) = 0 ↔
      pilotEvalSelect false x = -(pilotEvalSelect false y) := by
  exact pilotEvalSelect_false_add_eq_zero_iff_left x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect false (HeytingLean.Numbers.Surreal.Hyperseries.add x y) = 0 ↔
      -(pilotEvalSelect false x) = pilotEvalSelect false y := by
  exact pilotEvalSelect_false_add_eq_zero_iff_right x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEvalSelect true x = -(pilotEvalSelect true y) := by
  exact pilotEvalSelect_add_normalize_eq_zero_iff_left true x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      -(pilotEvalSelect true x) = pilotEvalSelect true y := by
  exact pilotEvalSelect_add_normalize_eq_zero_iff_right true x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEvalSelect false y = -(pilotEvalSelect false x) := by
  exact pilotEvalSelect_false_add_normalize_eq_zero_iff x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEvalSelect false x = -(pilotEvalSelect false y) := by
  exact pilotEvalSelect_false_add_normalize_eq_zero_iff_left x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      -(pilotEvalSelect false x) = pilotEvalSelect false y := by
  exact pilotEvalSelect_false_add_normalize_eq_zero_iff_right x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) = 0 ↔
      pilotEvalSelect true y = -(pilotEvalSelect true x) := by
  exact pilotEvalSelect_add_normalize_left_eq_zero_iff true x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) = 0 ↔
      pilotEvalSelect false y = -(pilotEvalSelect false x) := by
  exact pilotEvalSelect_false_add_normalize_left_eq_zero_iff x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) = 0 ↔
      -(pilotEvalSelect true x) = pilotEvalSelect true y := by
  exact pilotEvalSelect_add_normalize_left_eq_zero_iff_right true x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) = 0 ↔
      pilotEvalSelect false x = -(pilotEvalSelect false y) := by
  exact pilotEvalSelect_false_add_normalize_left_eq_zero_iff_left x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) = 0 ↔
      -(pilotEvalSelect false x) = pilotEvalSelect false y := by
  exact pilotEvalSelect_false_add_normalize_left_eq_zero_iff_right x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEvalSelect true x = -(pilotEvalSelect true y) := by
  exact pilotEvalSelect_add_normalize_right_eq_zero_iff_left true x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEvalSelect false y = -(pilotEvalSelect false x) := by
  exact pilotEvalSelect_false_add_normalize_right_eq_zero_iff x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      -(pilotEvalSelect true x) = pilotEvalSelect true y := by
  exact pilotEvalSelect_add_normalize_right_eq_zero_iff_right true x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      pilotEvalSelect false x = -(pilotEvalSelect false y) := by
  exact pilotEvalSelect_false_add_normalize_right_eq_zero_iff_left x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) = 0 ↔
      -(pilotEvalSelect false x) = pilotEvalSelect false y := by
  exact pilotEvalSelect_false_add_normalize_right_eq_zero_iff_right x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) =
      pilotEvalSelect true (HeytingLean.Numbers.Surreal.Hyperseries.add x y) := by
  exact pilotEvalSelect_add_normalize_left true x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) =
      pilotEvalSelect false (HeytingLean.Numbers.Surreal.Hyperseries.add x y) := by
  exact pilotEvalSelect_false_add_normalize_left x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          x (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) =
      pilotEvalSelect false (HeytingLean.Numbers.Surreal.Hyperseries.add x y) := by
  exact pilotEvalSelect_false_add_normalize_right x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize y)) =
      pilotEvalSelect false (HeytingLean.Numbers.Surreal.Hyperseries.add x y) := by
  exact pilotEvalSelect_false_add_normalize x y

example [HyperserialDescription Surreal] (x y : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.normalize
          (HeytingLean.Numbers.Surreal.Hyperseries.add x y)) =
      pilotEvalSelect false (HeytingLean.Numbers.Surreal.Hyperseries.add x y) := by
  exact pilotEvalSelect_false_normalize_add x y

example [HyperserialDescription Surreal] (x y z : PilotSeries) :
    pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.normalize y) z)) =
      pilotEvalSelect true x + pilotEvalSelect true y + pilotEvalSelect true z := by
  exact pilotEvalSelect_add_normalize_assoc true x y z

example [HyperserialDescription Surreal] (x y z : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)
          (HeytingLean.Numbers.Surreal.Hyperseries.add
            (HeytingLean.Numbers.Surreal.Hyperseries.normalize y) z)) =
      pilotEvalSelect false x + pilotEvalSelect false y + pilotEvalSelect false z := by
  exact pilotEvalSelect_false_add_normalize_assoc x y z

example [HyperserialDescription Surreal] (x y z : PilotSeries) :
    pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) =
      pilotEvalSelect true
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) z) ↔
        pilotEvalSelect true y = pilotEvalSelect true z := by
  exact pilotEvalSelect_add_normalize_cancel_left true x y z

example [HyperserialDescription Surreal] (x y z : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) y) =
      pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          (HeytingLean.Numbers.Surreal.Hyperseries.normalize x) z) ↔
        pilotEvalSelect false y = pilotEvalSelect false z := by
  exact pilotEvalSelect_false_add_normalize_cancel_left x y z

example [HyperserialDescription Surreal] (x y z : PilotSeries) :
    pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          y (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)) =
      pilotEvalSelect false
        (HeytingLean.Numbers.Surreal.Hyperseries.add
          z (HeytingLean.Numbers.Surreal.Hyperseries.normalize x)) ↔
        pilotEvalSelect false y = pilotEvalSelect false z := by
  exact pilotEvalSelect_false_add_normalize_cancel_right x y z

example [HyperserialDescription Surreal] (e : HExpr) :
    describeExpr e = describeExprWith surrealSemanticsDefault e := by
  exact describeExpr_eq_describeExprWith_default e

example [HyperserialDescription Surreal] (e : HExpr) :
    evalOmega (describeExpr e) = HExpr.eval surrealModel e := by
  exact evalOmega_describeExpr e

example [HyperserialDescription Surreal] : True := by
  let _ : Type _ := HSNo
  have _ : HSNo := X
  have _ := (evalRingHom (K := Surreal))
  have _ := (evalRingEquiv (K := Surreal))
  trivial

example [HyperserialDescription Surreal] : True := by
  let s : PilotSeries := []
  have _ := evalOmega_X
  have _ := evalOmega_eq_zero_of_ofPilotSeries_eq_zero (s := s)
  have _ := evalOmega_ofPilotSeries
  have _ := evalOmega_ofPilotSeriesWith_append
  have _ := evalOmega_ofPilotSeriesWith_monomial_zero
  have _ := evalOmega_ofPilotSeriesWith_mul_monomial
  have _ := evalOmega_ofPilotSeriesWith_normalize
  have _ := evalOmega_ofPilotSeries_add_assoc
  have _ := evalOmega_ofPilotSeries_add_cancel_left
  have _ := evalOmega_ofPilotSeries_add_cancel_right
  have _ := evalOmega_ofPilotSeries_add_comm
  have _ := evalOmega_ofPilotSeries_add_eq_zero_iff
  have _ := evalOmega_ofPilotSeries_add_eq_zero_iff_left
  have _ := evalOmega_ofPilotSeries_add_mul_monomial_zero_left_lhs
  have _ := evalOmega_ofPilotSeries_add_mul_monomial_zero_left_lhs_cancel
  have _ := evalOmega_ofPilotSeries_add_mul_monomial_zero_left_lhs_eq_iff
  have _ := evalOmega_ofPilotSeries_add_mul_monomial_zero_left_lhs_eq_iff_left
  have _ := evalOmega_ofPilotSeries_add_mul_monomial_zero_left_lhs_eq_iff_right
  have _ := evalOmega_ofPilotSeries_add_mul_monomial_zero_left_lhs_eq_zero_iff
  have _ := evalOmega_ofPilotSeries_add_mul_monomial_zero_left_rhs
  have _ := evalOmega_ofPilotSeries_add_mul_monomial_zero_left_rhs_cancel
  have _ := evalOmega_ofPilotSeries_add_mul_monomial_zero_left_rhs_eq_iff
  have _ := evalOmega_ofPilotSeries_add_mul_monomial_zero_left_rhs_eq_iff_left
  have _ := evalOmega_ofPilotSeries_add_mul_monomial_zero_left_rhs_eq_iff_right
  have _ := evalOmega_ofPilotSeries_add_mul_monomial_zero_left_rhs_eq_zero_iff
  have _ := evalOmega_ofPilotSeries_add_mul_monomial_zero_right_lhs
  have _ := evalOmega_ofPilotSeries_add_mul_monomial_zero_right_lhs_cancel
  have _ := evalOmega_ofPilotSeries_add_mul_monomial_zero_right_lhs_eq_iff
  have _ := evalOmega_ofPilotSeries_add_mul_monomial_zero_right_lhs_eq_iff_left
  have _ := evalOmega_ofPilotSeries_add_mul_monomial_zero_right_lhs_eq_iff_right
  have _ := evalOmega_ofPilotSeries_add_mul_monomial_zero_right_lhs_eq_zero_iff
  have _ := evalOmega_ofPilotSeries_add_mul_monomial_zero_right_rhs
  have _ := evalOmega_ofPilotSeries_add_mul_monomial_zero_right_rhs_cancel
  have _ := evalOmega_ofPilotSeries_add_mul_monomial_zero_right_rhs_eq_iff
  have _ := evalOmega_ofPilotSeries_add_mul_monomial_zero_right_rhs_eq_iff_left
  have _ := evalOmega_ofPilotSeries_add_mul_monomial_zero_right_rhs_eq_iff_right
  have _ := evalOmega_ofPilotSeries_add_mul_monomial_zero_right_rhs_eq_zero_iff
  have _ := evalOmega_ofPilotSeries_add_nil
  have _ := evalOmega_ofPilotSeries_add_normalize
  have _ := evalOmega_ofPilotSeries_add_normalize_assoc
  have _ := evalOmega_ofPilotSeries_add_normalize_cancel_left
  have _ := evalOmega_ofPilotSeries_add_normalize_cancel_right
  have _ := evalOmega_ofPilotSeries_add_normalize_eq_zero_iff
  have _ := evalOmega_ofPilotSeries_add_normalize_eq_zero_iff_left
  have _ := evalOmega_ofPilotSeries_add_normalize_left
  have _ := evalOmega_ofPilotSeries_add_normalize_left_eq_zero_iff
  have _ := evalOmega_ofPilotSeries_add_normalize_left_eq_zero_iff_left
  have _ := evalOmega_ofPilotSeries_add_normalize_right
  have _ := evalOmega_ofPilotSeries_add_normalize_right_eq_zero_iff
  have _ := evalOmega_ofPilotSeries_add_normalize_right_eq_zero_iff_left
  have _ := evalOmega_ofPilotSeries_append
  have _ := evalOmega_ofPilotSeries_append_assoc
  have _ := evalOmega_ofPilotSeries_append_nil
  have _ := evalOmega_ofPilotSeries_monomial_zero
  have _ := evalOmega_ofPilotSeries_mul_monomial
  have _ := evalOmega_ofPilotSeries_mul_monomial_eq_zero_iff
  have _ := evalOmega_ofPilotSeries_mul_monomial_eq_zero_of_coeff_mul_eq_zero
  have _ := evalOmega_ofPilotSeries_mul_monomial_zero_left
  have _ := evalOmega_ofPilotSeries_mul_monomial_zero_right
  have _ := evalOmega_ofPilotSeries_nil_add
  have _ := evalOmega_ofPilotSeries_nil_append
  have _ := evalOmega_ofPilotSeries_normalize
  have _ := evalOmega_ofPilotSeries_normalize_add
  have _ := (evalRingHom_apply (K := Surreal))
  have _ := existsUnique_hyperseries
  have _ := existsUnique_ofPilotSeries
  have _ := ofPilotSeries_add
  have _ := ofPilotSeries_add_assoc
  have _ := ofPilotSeries_add_cancel_left
  have _ := ofPilotSeries_add_cancel_right
  have _ := ofPilotSeries_add_comm
  have _ := ofPilotSeries_add_eq_zero_iff
  have _ := ofPilotSeries_add_eq_zero_iff_left
  have _ := ofPilotSeries_add_mul_monomial_zero_left_lhs
  have _ := ofPilotSeries_add_mul_monomial_zero_left_lhs_cancel
  have _ := ofPilotSeries_add_mul_monomial_zero_left_lhs_eq_iff
  have _ := ofPilotSeries_add_mul_monomial_zero_left_lhs_eq_iff_left
  have _ := ofPilotSeries_add_mul_monomial_zero_left_lhs_eq_iff_right
  have _ := ofPilotSeries_add_mul_monomial_zero_left_lhs_eq_zero_iff
  have _ := ofPilotSeries_add_mul_monomial_zero_left_rhs
  have _ := ofPilotSeries_add_mul_monomial_zero_left_rhs_cancel
  have _ := ofPilotSeries_add_mul_monomial_zero_left_rhs_eq_iff
  have _ := ofPilotSeries_add_mul_monomial_zero_left_rhs_eq_iff_left
  have _ := ofPilotSeries_add_mul_monomial_zero_left_rhs_eq_iff_right
  have _ := ofPilotSeries_add_mul_monomial_zero_left_rhs_eq_zero_iff
  have _ := ofPilotSeries_add_mul_monomial_zero_right_lhs
  have _ := ofPilotSeries_add_mul_monomial_zero_right_lhs_cancel
  have _ := ofPilotSeries_add_mul_monomial_zero_right_lhs_eq_iff
  have _ := ofPilotSeries_add_mul_monomial_zero_right_lhs_eq_iff_left
  have _ := ofPilotSeries_add_mul_monomial_zero_right_lhs_eq_iff_right
  have _ := ofPilotSeries_add_mul_monomial_zero_right_lhs_eq_zero_iff
  have _ := ofPilotSeries_add_mul_monomial_zero_right_rhs
  have _ := ofPilotSeries_add_mul_monomial_zero_right_rhs_cancel
  have _ := ofPilotSeries_add_mul_monomial_zero_right_rhs_eq_iff
  have _ := ofPilotSeries_add_mul_monomial_zero_right_rhs_eq_iff_left
  have _ := ofPilotSeries_add_mul_monomial_zero_right_rhs_eq_iff_right
  have _ := ofPilotSeries_add_mul_monomial_zero_right_rhs_eq_zero_iff
  have _ := ofPilotSeries_add_nil
  have _ := ofPilotSeries_add_normalize
  have _ := ofPilotSeries_add_normalize_assoc
  have _ := ofPilotSeries_add_normalize_cancel_left
  have _ := ofPilotSeries_add_normalize_cancel_right
  have _ := ofPilotSeries_add_normalize_eq_zero_iff
  have _ := ofPilotSeries_add_normalize_eq_zero_iff_left
  have _ := ofPilotSeries_add_normalize_left
  have _ := ofPilotSeries_add_normalize_left_eq_zero_iff
  have _ := ofPilotSeries_add_normalize_left_eq_zero_iff_left
  have _ := ofPilotSeries_add_normalize_right
  have _ := ofPilotSeries_add_normalize_right_eq_zero_iff
  have _ := ofPilotSeries_add_normalize_right_eq_zero_iff_left
  have _ := ofPilotSeries_append
  have _ := ofPilotSeries_append_assoc
  have _ := ofPilotSeries_append_nil
  have _ := ofPilotSeries_eq_iff_evalOmega_eq
  have _ := ofPilotSeries_eq_ofPilotSeriesWith_default
  have _ := ofPilotSeries_eq_zero_iff_evalOmega_eq_zero
  have _ := ofPilotSeries_eq_zero_of_evalOmega_eq_zero (s := s)
  have _ := ofPilotSeries_eq_zero_of_pilotEval_eq_zero (s := s)
  have _ := ofPilotSeries_monomial_zero
  have _ := ofPilotSeries_mul_monomial
  have _ := ofPilotSeries_mul_monomial_eq_zero_iff
  have _ := ofPilotSeries_mul_monomial_eq_zero_of_coeff_mul_eq_zero
  have _ := ofPilotSeries_mul_monomial_zero_left
  have _ := ofPilotSeries_mul_monomial_zero_right
  have _ := ofPilotSeries_nil
  have _ := ofPilotSeries_nil_add
  have _ := ofPilotSeries_nil_append
  have _ := ofPilotSeries_normalize
  have _ := ofPilotSeries_normalize_add
  have _ := pilotEvalSelect_false_eq_iff_ofPilotSeries_eq
  have _ := pilotEvalSelect_false_eq_zero_iff_ofPilotSeries_eq_zero
  trivial

end
end Numbers
end Tests
end HeytingLean
