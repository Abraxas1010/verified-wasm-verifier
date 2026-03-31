import HeytingLean.Hyperseries
import HeytingLean.Numbers.Surreal.Hyperseries

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Hyperseries
open HeytingLean.Hyperseries.BridgePilot
open HeytingLean.Numbers.Ordinal
open HeytingLean.Numbers.Surreal.Hyperseries

private def intModel : HyperserialModel Int where
  omega := 2
  exp := fun x => x
  log := fun x => x
  hyperExp := fun _ x => x + 1
  hyperLog := fun _ x => x - 1

private def ratModel : HyperserialModel Rat where
  omega := 0
  exp := fun x => x
  log := fun x => x
  hyperExp := fun _ x => x
  hyperLog := fun _ x => x

private def sA : Series :=
  [{ coeff := 0, exp := OrdinalCNF.ofNat 5 }, { coeff := 3, exp := OrdinalCNF.ofNat 1 }]

private def sB : Series :=
  monomial (-2) (OrdinalCNF.omega + OrdinalCNF.ofNat 1)

example :
    seriesSem intModel (add sA sB) = seriesSem intModel sA + seriesSem intModel sB := by
  exact seriesSem_add (M := intModel) sA sB

example :
    HExpr.eval intModel (ofSeries (normalize sA)) = HExpr.eval intModel (ofSeries sA) := by
  exact eval_ofSeries_normalize (M := intModel) sA

example :
    HExpr.eval intModel
        (ofSeries (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))) =
      HExpr.eval intModel (ofSeries (monomial (-6) (OrdinalCNF.ofNat 1 + OrdinalCNF.ofNat 2))) := by
  exact eval_ofSeries_mul_monomial (M := intModel) 2 (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2)

example :
    HExpr.eval intModel (ofSeries (monomial 7 (OrdinalCNF.ofNat 4))) =
      (7 : Int) * intModel.hyperExp (NONote.repr (OrdinalCNF.ofNat 4)) intModel.omega := by
  exact eval_ofSeries_monomial (M := intModel) 7 (OrdinalCNF.ofNat 4)

example :
    HExpr.eval intModel (ofSeries sA) =
      sA.foldr (fun t acc => termSem intModel t + acc) 0 := by
  exact eval_ofSeries_eq_foldr (M := intModel) sA

example :
    seriesSemQ ratModel (add sA sB) = seriesSemQ ratModel sA + seriesSemQ ratModel sB := by
  exact seriesSemQ_add (M := ratModel) sA sB

example :
    HExprQ.eval ratModel (ofSeriesQ (normalize sA)) = HExprQ.eval ratModel (ofSeriesQ sA) := by
  exact eval_ofSeriesQ_normalize (M := ratModel) sA

example :
    HExprQ.eval ratModel
        (ofSeriesQ (mul (monomial 5 (OrdinalCNF.ofNat 0)) (monomial (-2) (OrdinalCNF.ofNat 3)))) =
      HExprQ.eval ratModel (ofSeriesQ (monomial (-10) (OrdinalCNF.ofNat 0 + OrdinalCNF.ofNat 3))) := by
  exact eval_ofSeriesQ_mul_monomial (M := ratModel) 5 (-2) (OrdinalCNF.ofNat 0) (OrdinalCNF.ofNat 3)

example :
    HExprQ.eval ratModel (ofSeriesQ (monomial (-11) (OrdinalCNF.omega + OrdinalCNF.ofNat 2))) =
      ((-11 : Int) : Rat) *
        ratModel.hyperExp (NONote.repr (OrdinalCNF.omega + OrdinalCNF.ofNat 2)) ratModel.omega := by
  exact eval_ofSeriesQ_monomial (M := ratModel) (-11) (OrdinalCNF.omega + OrdinalCNF.ofNat 2)

example :
    HExprQ.eval ratModel (ofSeriesQ sB) =
      sB.foldr (fun t acc => termSemQ ratModel t + acc) 0 := by
  exact eval_ofSeriesQ_eq_foldr (M := ratModel) sB

example :
    liftIntToRat (ofSeries sA) = ofSeriesQ sA := by
  exact liftIntToRat_ofSeries sA

example :
    HExprQ.eval ratModel (ofSeriesQ sA) = HExpr.eval ratModel (ofSeries sA) := by
  exact eval_ofSeriesQ_eq_eval_ofSeries (M := ratModel) sA

example :
    HExpr.eval ratModel (ofSeries (sA ++ sB)) =
      HExpr.eval ratModel (ofSeries sA) + HExpr.eval ratModel (ofSeries sB) := by
  exact eval_ofPilot_append (M := ratModel) sA sB

example :
    HExprQ.eval ratModel (ofSeriesQ (normalize sA)) = HExprQ.eval ratModel (ofSeriesQ sA) := by
  exact eval_ofPilotQ_normalize (M := ratModel) sA

example : HExpr.eval surrealModel (ExprC.X : HExpr) = omegaSurreal := by
  simp

example :
    HExpr.eval surrealModel (ofSeries (sA ++ sB)) =
      HExpr.eval surrealModel (ofSeries sA) + HExpr.eval surrealModel (ofSeries sB) := by
  exact eval_ofPilot_append (M := surrealModel) sA sB

section NameWiringSmoke

#check expExpr
#check expExprQ
#check ofTerm
#check ofTermQ
#check ofSeriesWith
#check ofSeriesQWith
#check seriesSemWith
#check seriesSemQWith
#check ofSeriesWith_nil
#check ofSeriesWith_cons
#check ofSeriesWith_append
#check ofSeries_nil
#check ofSeries_add
#check ofSeries_mul_monomial
#check ofSeriesQWith_nil
#check ofSeriesQWith_cons
#check ofSeriesQWith_append
#check ofSeriesQ_nil
#check ofSeriesQ_add
#check ofSeriesQ_mul_monomial
#check liftIntToRat_C
#check liftIntToRat_X
#check liftIntToRat_expExpr
#check liftIntToRat_ofTerm
#check liftIntToRat_ofSeriesWith
#check eval_liftIntToRat
#check eval_expExpr
#check eval_ofTerm
#check eval_ofSeriesWith
#check eval_ofSeries
#check seriesSem_nil
#check seriesSem_eq_foldr
#check seriesSem_monomial
#check seriesSemWith_append
#check seriesSemWith_eq_add
#check eval_ofSeries_add
#check seriesSemWith_normalize
#check seriesSem_normalize
#check eval_expExprQ
#check eval_ofTermQ
#check eval_ofSeriesQWith
#check eval_ofSeriesQ
#check seriesSemQ_nil
#check seriesSemQ_eq_foldr
#check seriesSemQ_monomial
#check seriesSemQWith_append
#check seriesSemQWith_eq_add
#check eval_ofSeriesQ_add
#check seriesSemQWith_normalize
#check seriesSemQ_normalize
#check eval_ofPilot_zero
#check eval_ofPilot_monomial
#check eval_ofPilot_normalize
#check eval_ofPilotQ_zero
#check eval_ofPilotQ_monomial
#check eval_ofPilotQ_append

end NameWiringSmoke

end Numbers
end Tests
end HeytingLean
