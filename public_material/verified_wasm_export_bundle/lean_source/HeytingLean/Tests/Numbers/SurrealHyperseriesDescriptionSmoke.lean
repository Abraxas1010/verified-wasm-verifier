import HeytingLean.Hyperseries

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Hyperseries
open HeytingLean.Numbers.Ordinal
open HeytingLean.Numbers.Surreal.Hyperseries

noncomputable instance : HyperserialDescription Surreal :=
  HyperserialDescription.idDescription Surreal

private def sA : Series :=
  [{ coeff := 0, exp := OrdinalCNF.ofNat 5 }, { coeff := 3, exp := OrdinalCNF.ofNat 1 }]

private def sB : Series :=
  monomial (-2) (OrdinalCNF.omega + OrdinalCNF.ofNat 1)

example : evalOmega X = omegaSurreal := by
  simp

example (a : Surreal) : ∃! h : HSNo, evalOmega h = a := by
  simpa using (existsUnique_hyperseries a)

example :
    evalOmega (ofPilotSeries sA) = HExpr.eval surrealModel (BridgePilot.ofSeries sA) := by
  simpa using (evalOmega_ofPilotSeries sA)

example : ofPilotSeries ([] : Series) = (0 : HSNo) := by
  simp

example : pilotEval ([] : Series) = (0 : Surreal) := by
  simp

example :
    pilotEval (monomial 7 (OrdinalCNF.ofNat 2)) =
      HExpr.eval surrealModel (BridgePilot.ofSeries (monomial 7 (OrdinalCNF.ofNat 2))) := by
  exact pilotEval_monomial 7 (OrdinalCNF.ofNat 2)

example :
    evalOmega (ofPilotSeries (sA ++ sB)) =
      evalOmega (ofPilotSeries sA) + evalOmega (ofPilotSeries sB) := by
  simpa using (evalOmega_ofPilotSeries_append sA sB)

example :
    ofPilotSeries (sA ++ sB) = ofPilotSeries sA + ofPilotSeries sB := by
  simpa using (ofPilotSeries_append sA sB)

example :
    ofPilotSeries (add sA sB) = ofPilotSeries sA + ofPilotSeries sB := by
  simpa using (ofPilotSeries_add sA sB)

example :
    ofPilotSeries (sA ++ []) = ofPilotSeries sA := by
  simp

example :
    ofPilotSeries ([] ++ sA) = ofPilotSeries sA := by
  simp

example :
    ofPilotSeries ((sA ++ sB) ++ sA) =
      ofPilotSeries sA + ofPilotSeries sB + ofPilotSeries sA := by
  simpa using (ofPilotSeries_append_assoc sA sB sA)

example :
    ofPilotSeries (add sA []) = ofPilotSeries sA := by
  simp

example :
    ofPilotSeries (add [] sA) = ofPilotSeries sA := by
  simp

example :
    ofPilotSeries (add (add sA sB) sA) =
      ofPilotSeries sA + ofPilotSeries sB + ofPilotSeries sA := by
  simpa using (ofPilotSeries_add_assoc sA sB sA)

example :
    ofPilotSeries (add sA sB) = ofPilotSeries (add sB sA) := by
  simpa using (ofPilotSeries_add_comm sA sB)

example :
    evalOmega (ofPilotSeries (sA ++ [])) = evalOmega (ofPilotSeries sA) := by
  exact (evalOmega_ofPilotSeries_append_nil sA)

example :
    evalOmega (ofPilotSeries ([] ++ sA)) = evalOmega (ofPilotSeries sA) := by
  exact (evalOmega_ofPilotSeries_nil_append sA)

example :
    evalOmega (ofPilotSeries ((sA ++ sB) ++ sA)) =
      evalOmega (ofPilotSeries sA) + evalOmega (ofPilotSeries sB) + evalOmega (ofPilotSeries sA) := by
  simpa using (evalOmega_ofPilotSeries_append_assoc sA sB sA)

example :
    evalOmega (ofPilotSeries (add sA [])) = evalOmega (ofPilotSeries sA) := by
  exact (evalOmega_ofPilotSeries_add_nil sA)

example :
    evalOmega (ofPilotSeries (add [] sA)) = evalOmega (ofPilotSeries sA) := by
  exact (evalOmega_ofPilotSeries_nil_add sA)

example :
    evalOmega (ofPilotSeries (add (add sA sB) sA)) =
      evalOmega (ofPilotSeries sA) + evalOmega (ofPilotSeries sB) + evalOmega (ofPilotSeries sA) := by
  simpa using (evalOmega_ofPilotSeries_add_assoc sA sB sA)

example :
    evalOmega (ofPilotSeries (add sA sB)) = evalOmega (ofPilotSeries (add sB sA)) := by
  simpa using (evalOmega_ofPilotSeries_add_comm sA sB)

example :
    evalOmega (ofPilotSeries ([] : Series)) = 0 := by
  exact evalOmega_eq_zero_of_ofPilotSeries_eq_zero (s := ([] : Series)) ofPilotSeries_nil

example :
    ofPilotSeries ([] : Series) = 0 := by
  exact ofPilotSeries_eq_zero_of_evalOmega_eq_zero (s := ([] : Series)) (by simp)

example :
    ofPilotSeries ([] : Series) = 0 := by
  exact ofPilotSeries_eq_zero_of_pilotEval_eq_zero (s := ([] : Series)) (by simp)

example :
    pilotEval ([] : Series) = 0 := by
  exact pilotEval_eq_zero_of_ofPilotSeries_eq_zero (s := ([] : Series)) ofPilotSeries_nil

example :
    ofPilotSeries (add sA sB) = ofPilotSeries (add sA sB) ↔ ofPilotSeries sB = ofPilotSeries sB := by
  simp

example :
    ofPilotSeries (add sB sA) = ofPilotSeries (add sB sA) ↔ ofPilotSeries sA = ofPilotSeries sA := by
  simp

example :
    ofPilotSeries (add ([] : Series) ([] : Series)) = 0 := by
  exact (ofPilotSeries_add_eq_zero_iff ([] : Series) []).2 (by simp)

example :
    ofPilotSeries (add (normalize ([] : Series)) ([] : Series)) = 0 := by
  exact (ofPilotSeries_add_normalize_left_eq_zero_iff ([] : Series) []).2 (by simp)

example :
    ofPilotSeries (add ([] : Series) (normalize ([] : Series))) = 0 := by
  exact (ofPilotSeries_add_normalize_right_eq_zero_iff ([] : Series) []).2 (by simp)

example :
    ofPilotSeries (add (normalize ([] : Series)) (normalize ([] : Series))) = 0 := by
  exact (ofPilotSeries_add_normalize_eq_zero_iff ([] : Series) []).2 (by simp)

example :
    ofPilotSeries (add ([] : Series) ([] : Series)) = 0 := by
  exact (ofPilotSeries_add_eq_zero_iff_left ([] : Series) []).2 (by simp)

example :
    ofPilotSeries (add (normalize ([] : Series)) ([] : Series)) = 0 := by
  exact (ofPilotSeries_add_normalize_left_eq_zero_iff_left ([] : Series) []).2 (by simp)

example :
    ofPilotSeries (add ([] : Series) (normalize ([] : Series))) = 0 := by
  exact (ofPilotSeries_add_normalize_right_eq_zero_iff_left ([] : Series) []).2 (by simp)

example :
    ofPilotSeries (add (normalize ([] : Series)) (normalize ([] : Series))) = 0 := by
  exact (ofPilotSeries_add_normalize_eq_zero_iff_left ([] : Series) []).2 (by simp)

example :
    pilotEval (add sA sB) = pilotEval sA + pilotEval sB := by
  simpa using (pilotEval_add sA sB)

example :
    pilotEval (add sA sB) = pilotEval (add sB sA) := by
  simpa using (pilotEval_add_comm sA sB)

example :
    pilotEval (add sA sB) = pilotEval (add sA sB) ↔ pilotEval sB = pilotEval sB := by
  simp

example :
    pilotEval (add sB sA) = pilotEval (add sB sA) ↔ pilotEval sA = pilotEval sA := by
  simp

example :
    pilotEval (add ([] : Series) ([] : Series)) = 0 := by
  exact (pilotEval_add_eq_zero_iff ([] : Series) []).2 (by simp)

example :
    pilotEval (add (normalize ([] : Series)) ([] : Series)) = 0 := by
  exact (pilotEval_add_normalize_left_eq_zero_iff ([] : Series) []).2 (by simp)

example :
    pilotEval (add ([] : Series) (normalize ([] : Series))) = 0 := by
  exact (pilotEval_add_normalize_right_eq_zero_iff ([] : Series) []).2 (by simp)

example :
    pilotEval (add (normalize ([] : Series)) (normalize ([] : Series))) = 0 := by
  exact (pilotEval_add_normalize_eq_zero_iff ([] : Series) []).2 (by simp)

example :
    pilotEval (add ([] : Series) ([] : Series)) = 0 := by
  exact (pilotEval_add_eq_zero_iff_left ([] : Series) []).2 (by simp)

example :
    pilotEval (add (normalize ([] : Series)) ([] : Series)) = 0 := by
  exact (pilotEval_add_normalize_left_eq_zero_iff_left ([] : Series) []).2 (by simp)

example :
    pilotEval (add ([] : Series) (normalize ([] : Series))) = 0 := by
  exact (pilotEval_add_normalize_right_eq_zero_iff_left ([] : Series) []).2 (by simp)

example :
    pilotEval (add (normalize ([] : Series)) (normalize ([] : Series))) = 0 := by
  exact (pilotEval_add_normalize_eq_zero_iff_left ([] : Series) []).2 (by simp)

example :
    ofPilotSeries (add (normalize sA) sB) = ofPilotSeries (add sA sB) := by
  simpa using (ofPilotSeries_add_normalize_left sA sB)

example :
    ofPilotSeries (add sA (normalize sB)) = ofPilotSeries (add sA sB) := by
  simpa using (ofPilotSeries_add_normalize_right sA sB)

example :
    ofPilotSeries (add (normalize sA) (normalize sB)) = ofPilotSeries (add sA sB) := by
  simpa using (ofPilotSeries_add_normalize sA sB)

example :
    ofPilotSeries (normalize (add sA sB)) = ofPilotSeries (add sA sB) := by
  simpa using (ofPilotSeries_normalize_add sA sB)

example :
    ofPilotSeries (add (normalize sA) (add (normalize sB) sA)) =
      ofPilotSeries sA + ofPilotSeries sB + ofPilotSeries sA := by
  simpa using (ofPilotSeries_add_normalize_assoc sA sB sA)

example :
    ofPilotSeries (add (normalize sA) sB) = ofPilotSeries (add (normalize sA) sB) := by
  exact (ofPilotSeries_add_normalize_cancel_left sA sB sB).2 rfl

example :
    ofPilotSeries (add sB (normalize sA)) = ofPilotSeries (add sB (normalize sA)) := by
  exact (ofPilotSeries_add_normalize_cancel_right sA sB sB).2 rfl

example :
    pilotEval (add (normalize sA) sB) = pilotEval (add sA sB) := by
  simpa using (pilotEval_add_normalize_left sA sB)

example :
    pilotEval (add sA (normalize sB)) = pilotEval (add sA sB) := by
  simpa using (pilotEval_add_normalize_right sA sB)

example :
    pilotEval (add (normalize sA) (normalize sB)) = pilotEval (add sA sB) := by
  simpa using (pilotEval_add_normalize sA sB)

example :
    pilotEval (normalize (add sA sB)) = pilotEval (add sA sB) := by
  simpa using (pilotEval_normalize_add sA sB)

example :
    pilotEval (add (normalize sA) (add (normalize sB) sA)) =
      pilotEval sA + pilotEval sB + pilotEval sA := by
  simpa using (pilotEval_add_normalize_assoc sA sB sA)

example :
    pilotEval (add (normalize sA) sB) = pilotEval (add (normalize sA) sB) := by
  exact (pilotEval_add_normalize_cancel_left sA sB sB).2 rfl

example :
    pilotEval (add sB (normalize sA)) = pilotEval (add sB (normalize sA)) := by
  exact (pilotEval_add_normalize_cancel_right sA sB sB).2 rfl

example :
    pilotEval ((sA ++ sB) ++ sA) = pilotEval sA + pilotEval sB + pilotEval sA := by
  simpa using (pilotEval_append_assoc sA sB sA)

example :
    pilotEval (add (add sA sB) sA) = pilotEval sA + pilotEval sB + pilotEval sA := by
  simpa using (pilotEval_add_assoc sA sB sA)

example :
    evalOmega (ofPilotSeries (normalize sA)) = evalOmega (ofPilotSeries sA) := by
  simpa using (evalOmega_ofPilotSeries_normalize sA)

example :
    evalOmega (ofPilotSeries (add (normalize sA) sB)) =
      evalOmega (ofPilotSeries (add sA sB)) := by
  simpa using (evalOmega_ofPilotSeries_add_normalize_left sA sB)

example :
    evalOmega (ofPilotSeries (add sA (normalize sB))) =
      evalOmega (ofPilotSeries (add sA sB)) := by
  simpa using (evalOmega_ofPilotSeries_add_normalize_right sA sB)

example :
    evalOmega (ofPilotSeries (add (normalize sA) (normalize sB))) =
      evalOmega (ofPilotSeries (add sA sB)) := by
  simpa using (evalOmega_ofPilotSeries_add_normalize sA sB)

example :
    evalOmega (ofPilotSeries (normalize (add sA sB))) =
      evalOmega (ofPilotSeries (add sA sB)) := by
  simpa using (evalOmega_ofPilotSeries_normalize_add sA sB)

example :
    evalOmega (ofPilotSeries (add (normalize sA) (add (normalize sB) sA))) =
      evalOmega (ofPilotSeries sA) + evalOmega (ofPilotSeries sB) + evalOmega (ofPilotSeries sA) := by
  simpa using (evalOmega_ofPilotSeries_add_normalize_assoc sA sB sA)

example :
    evalOmega (ofPilotSeries (add sA sB)) = evalOmega (ofPilotSeries (add sA sB)) := by
  exact (evalOmega_ofPilotSeries_add_cancel_left sA sB sB).2 rfl

example :
    evalOmega (ofPilotSeries (add sB sA)) = evalOmega (ofPilotSeries (add sB sA)) := by
  exact (evalOmega_ofPilotSeries_add_cancel_right sA sB sB).2 rfl

example :
    evalOmega (ofPilotSeries (add ([] : Series) ([] : Series))) = 0 := by
  exact (evalOmega_ofPilotSeries_add_eq_zero_iff ([] : Series) []).2 (by simp)

example :
    evalOmega (ofPilotSeries (add ([] : Series) ([] : Series))) = 0 := by
  exact (evalOmega_ofPilotSeries_add_eq_zero_iff_left ([] : Series) []).2 (by simp)

example :
    evalOmega (ofPilotSeries (add (normalize sA) sB)) =
      evalOmega (ofPilotSeries (add (normalize sA) sB)) := by
  exact (evalOmega_ofPilotSeries_add_normalize_cancel_left sA sB sB).2 rfl

example :
    evalOmega (ofPilotSeries (add sB (normalize sA))) =
      evalOmega (ofPilotSeries (add sB (normalize sA))) := by
  exact (evalOmega_ofPilotSeries_add_normalize_cancel_right sA sB sB).2 rfl

example :
    evalOmega (ofPilotSeries (add (normalize ([] : Series)) ([] : Series))) = 0 := by
  exact (evalOmega_ofPilotSeries_add_normalize_left_eq_zero_iff ([] : Series) []).2 (by simp)

example :
    evalOmega (ofPilotSeries (add ([] : Series) (normalize ([] : Series)))) = 0 := by
  exact (evalOmega_ofPilotSeries_add_normalize_right_eq_zero_iff ([] : Series) []).2 (by simp)

example :
    evalOmega
        (ofPilotSeries (add (normalize ([] : Series)) (normalize ([] : Series)))) = 0 := by
  exact (evalOmega_ofPilotSeries_add_normalize_eq_zero_iff ([] : Series) []).2 (by simp)

example :
    ofPilotSeries (normalize sA) = ofPilotSeries sA := by
  simpa using (ofPilotSeries_normalize sA)

example :
    pilotEval (normalize sA) = pilotEval sA := by
  simpa using (pilotEval_normalize sA)

example :
    pilotEval (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2))) =
      pilotEval (monomial (-6) (OrdinalCNF.ofNat 1 + OrdinalCNF.ofNat 2)) := by
  exact pilotEval_mul_monomial 2 (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2)

example :
    ofPilotSeries (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2))) =
      ofPilotSeries (monomial (-6) (OrdinalCNF.ofNat 1 + OrdinalCNF.ofNat 2)) := by
  exact ofPilotSeries_mul_monomial 2 (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2)

example :
    evalOmega
        (ofPilotSeries (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))) =
      evalOmega (ofPilotSeries (monomial (-6) (OrdinalCNF.ofNat 1 + OrdinalCNF.ofNat 2))) := by
  exact evalOmega_ofPilotSeries_mul_monomial 2 (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2)

example :
    ofPilotSeries (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2))) = 0 := by
  exact ofPilotSeries_mul_monomial_zero_left (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2)

example :
    ofPilotSeries (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2))) = 0 := by
  exact ofPilotSeries_mul_monomial_zero_right 2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2)

example :
    evalOmega
        (ofPilotSeries (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))) = 0 := by
  exact evalOmega_ofPilotSeries_mul_monomial_zero_left (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2)

example :
    evalOmega
        (ofPilotSeries (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))) = 0 := by
  exact evalOmega_ofPilotSeries_mul_monomial_zero_right 2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2)

example :
    pilotEval (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2))) = 0 := by
  exact pilotEval_mul_monomial_zero_left (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2)

example :
    pilotEval (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2))) = 0 := by
  exact pilotEval_mul_monomial_zero_right 2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2)

example :
    ofPilotSeries (mul (monomial 5 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2))) = 0 := by
  exact ofPilotSeries_mul_monomial_eq_zero_of_coeff_mul_eq_zero 5 0
    (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) (by simp)

example :
    evalOmega
        (ofPilotSeries (mul (monomial 5 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))) = 0 := by
  exact evalOmega_ofPilotSeries_mul_monomial_eq_zero_of_coeff_mul_eq_zero 5 0
    (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) (by simp)

example :
    pilotEval (mul (monomial 5 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2))) = 0 := by
  exact pilotEval_mul_monomial_eq_zero_of_coeff_mul_eq_zero 5 0
    (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) (by simp)

example :
    ofPilotSeries
        (add
          (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))
          sA) = ofPilotSeries sA := by
  exact ofPilotSeries_add_mul_monomial_zero_left_lhs (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA

example :
    ofPilotSeries
        (add
          sA
          (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))) = ofPilotSeries sA := by
  exact ofPilotSeries_add_mul_monomial_zero_right_rhs sA 2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2)

example :
    evalOmega
        (ofPilotSeries
          (add
            (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))
            sA)) = evalOmega (ofPilotSeries sA) := by
  exact
    evalOmega_ofPilotSeries_add_mul_monomial_zero_left_lhs
      (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA

example :
    evalOmega
        (ofPilotSeries
          (add
            sA
            (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2))))) =
      evalOmega (ofPilotSeries sA) := by
  exact
    evalOmega_ofPilotSeries_add_mul_monomial_zero_right_rhs
      sA 2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2)

example :
    pilotEval
        (add
          (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))
          sA) = pilotEval sA := by
  exact pilotEval_add_mul_monomial_zero_left_lhs (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA

example :
    pilotEval
        (add
          sA
          (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))) = pilotEval sA := by
  exact pilotEval_add_mul_monomial_zero_right_rhs sA 2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2)

example :
    ofPilotSeries.{0,1}
        (add
          (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))
          sA) =
      ofPilotSeries.{0,1}
        (add
          (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))
          sB) ↔
      ofPilotSeries.{0,1} sA = ofPilotSeries.{0,1} sB := by
  exact (@ofPilotSeries_add_mul_monomial_zero_left_lhs_cancel.{1, 0}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    ofPilotSeries.{0,1}
        (add
          sA
          (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))) =
      ofPilotSeries.{0,1}
        (add
          sB
          (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))) ↔
      ofPilotSeries.{0,1} sA = ofPilotSeries.{0,1} sB := by
  exact (@ofPilotSeries_add_mul_monomial_zero_right_rhs_cancel.{1, 0}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    ofPilotSeries.{0,1}
        (add
          (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))
          sA) =
      ofPilotSeries.{0,1}
        (add
          (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))
          sB) ↔
      ofPilotSeries.{0,1} sA = ofPilotSeries.{0,1} sB := by
  exact (@ofPilotSeries_add_mul_monomial_zero_right_lhs_cancel.{1, 0}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    ofPilotSeries.{0,1}
        (add
          sA
          (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))) =
      ofPilotSeries.{0,1}
        (add
          sB
          (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))) ↔
      ofPilotSeries.{0,1} sA = ofPilotSeries.{0,1} sB := by
  exact (@ofPilotSeries_add_mul_monomial_zero_left_rhs_cancel.{1, 0}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    evalOmega.{0,1}
        (ofPilotSeries.{0,1}
          (add
            (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))
            sA)) =
      evalOmega.{0,1}
        (ofPilotSeries.{0,1}
          (add
            (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))
            sB)) ↔
      evalOmega.{0,1} (ofPilotSeries.{0,1} sA) = evalOmega.{0,1} (ofPilotSeries.{0,1} sB) := by
  exact (@evalOmega_ofPilotSeries_add_mul_monomial_zero_left_lhs_cancel.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    evalOmega.{0,1}
        (ofPilotSeries.{0,1}
          (add
            sA
            (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2))))) =
      evalOmega.{0,1}
        (ofPilotSeries.{0,1}
          (add
            sB
            (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2))))) ↔
      evalOmega.{0,1} (ofPilotSeries.{0,1} sA) = evalOmega.{0,1} (ofPilotSeries.{0,1} sB) := by
  exact (@evalOmega_ofPilotSeries_add_mul_monomial_zero_right_rhs_cancel.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    evalOmega.{0,1}
        (ofPilotSeries.{0,1}
          (add
            (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))
            sA)) =
      evalOmega.{0,1}
        (ofPilotSeries.{0,1}
          (add
            (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))
            sB)) ↔
      evalOmega.{0,1} (ofPilotSeries.{0,1} sA) = evalOmega.{0,1} (ofPilotSeries.{0,1} sB) := by
  exact (@evalOmega_ofPilotSeries_add_mul_monomial_zero_right_lhs_cancel.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    evalOmega.{0,1}
        (ofPilotSeries.{0,1}
          (add
            sA
            (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2))))) =
      evalOmega.{0,1}
        (ofPilotSeries.{0,1}
          (add
            sB
            (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2))))) ↔
      evalOmega.{0,1} (ofPilotSeries.{0,1} sA) = evalOmega.{0,1} (ofPilotSeries.{0,1} sB) := by
  exact (@evalOmega_ofPilotSeries_add_mul_monomial_zero_left_rhs_cancel.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    pilotEval.{0,1}
        (add
          (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))
          sA) =
      pilotEval.{0,1}
        (add
          (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))
          sB) ↔
      pilotEval.{0,1} sA = pilotEval.{0,1} sB := by
  exact (@pilotEval_add_mul_monomial_zero_left_lhs_cancel.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    pilotEval.{0,1}
        (add
          sA
          (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))) =
      pilotEval.{0,1}
        (add
          sB
          (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))) ↔
      pilotEval.{0,1} sA = pilotEval.{0,1} sB := by
  exact (@pilotEval_add_mul_monomial_zero_right_rhs_cancel.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    pilotEval.{0,1}
        (add
          (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))
          sA) =
      pilotEval.{0,1}
        (add
          (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))
          sB) ↔
      pilotEval.{0,1} sA = pilotEval.{0,1} sB := by
  exact (@pilotEval_add_mul_monomial_zero_right_lhs_cancel.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    pilotEval.{0,1}
        (add
          sA
          (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))) =
      pilotEval.{0,1}
        (add
          sB
          (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))) ↔
      pilotEval.{0,1} sA = pilotEval.{0,1} sB := by
  exact (@pilotEval_add_mul_monomial_zero_left_rhs_cancel.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    ofPilotSeries.{0,1}
        (add
          (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))
          sA) = 0 ↔
      ofPilotSeries.{0,1} sA = 0 := by
  exact (@ofPilotSeries_add_mul_monomial_zero_left_lhs_eq_zero_iff.{1, 0}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA)

example :
    ofPilotSeries.{0,1}
        (add
          (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))
          sA) = 0 ↔
      ofPilotSeries.{0,1} sA = 0 := by
  exact (@ofPilotSeries_add_mul_monomial_zero_right_lhs_eq_zero_iff.{1, 0}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA)

example :
    ofPilotSeries.{0,1}
        (add
          sA
          (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))) = 0 ↔
      ofPilotSeries.{0,1} sA = 0 := by
  exact (@ofPilotSeries_add_mul_monomial_zero_left_rhs_eq_zero_iff.{1, 0}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    sA (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2))

example :
    ofPilotSeries.{0,1}
        (add
          sA
          (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))) = 0 ↔
      ofPilotSeries.{0,1} sA = 0 := by
  exact (@ofPilotSeries_add_mul_monomial_zero_right_rhs_eq_zero_iff.{1, 0}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    sA 2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2))

example :
    evalOmega.{0,1}
        (ofPilotSeries.{0,1}
          (add
            (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))
            sA)) = 0 ↔
      evalOmega.{0,1} (ofPilotSeries.{0,1} sA) = 0 := by
  exact (@evalOmega_ofPilotSeries_add_mul_monomial_zero_left_lhs_eq_zero_iff.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA)

example :
    evalOmega.{0,1}
        (ofPilotSeries.{0,1}
          (add
            (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))
            sA)) = 0 ↔
      evalOmega.{0,1} (ofPilotSeries.{0,1} sA) = 0 := by
  exact (@evalOmega_ofPilotSeries_add_mul_monomial_zero_right_lhs_eq_zero_iff.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA)

example :
    evalOmega.{0,1}
        (ofPilotSeries.{0,1}
          (add
            sA
            (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2))))) = 0 ↔
      evalOmega.{0,1} (ofPilotSeries.{0,1} sA) = 0 := by
  exact (@evalOmega_ofPilotSeries_add_mul_monomial_zero_left_rhs_eq_zero_iff.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    sA (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2))

example :
    evalOmega.{0,1}
        (ofPilotSeries.{0,1}
          (add
            sA
            (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2))))) = 0 ↔
      evalOmega.{0,1} (ofPilotSeries.{0,1} sA) = 0 := by
  exact (@evalOmega_ofPilotSeries_add_mul_monomial_zero_right_rhs_eq_zero_iff.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    sA 2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2))

example :
    pilotEval.{0,1}
        (add
          (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))
          sA) = 0 ↔
      pilotEval.{0,1} sA = 0 := by
  exact (@pilotEval_add_mul_monomial_zero_left_lhs_eq_zero_iff.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA)

example :
    pilotEval.{0,1}
        (add
          (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))
          sA) = 0 ↔
      pilotEval.{0,1} sA = 0 := by
  exact (@pilotEval_add_mul_monomial_zero_right_lhs_eq_zero_iff.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA)

example :
    pilotEval.{0,1}
        (add
          sA
          (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))) = 0 ↔
      pilotEval.{0,1} sA = 0 := by
  exact (@pilotEval_add_mul_monomial_zero_left_rhs_eq_zero_iff.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    sA (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2))

example :
    pilotEval.{0,1}
        (add
          sA
          (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))) = 0 ↔
      pilotEval.{0,1} sA = 0 := by
  exact (@pilotEval_add_mul_monomial_zero_right_rhs_eq_zero_iff.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    sA 2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2))

example :
    ofPilotSeries.{0,1}
        (add
          (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))
          sA) =
      ofPilotSeries.{0,1} sB ↔
      ofPilotSeries.{0,1} sA = ofPilotSeries.{0,1} sB := by
  exact (@ofPilotSeries_add_mul_monomial_zero_left_lhs_eq_iff.{1, 0}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    ofPilotSeries.{0,1}
        (add
          (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))
          sA) =
      ofPilotSeries.{0,1} sB ↔
      ofPilotSeries.{0,1} sA = ofPilotSeries.{0,1} sB := by
  exact (@ofPilotSeries_add_mul_monomial_zero_right_lhs_eq_iff.{1, 0}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    ofPilotSeries.{0,1}
        (add
          sA
          (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))) =
      ofPilotSeries.{0,1} sB ↔
      ofPilotSeries.{0,1} sA = ofPilotSeries.{0,1} sB := by
  exact (@ofPilotSeries_add_mul_monomial_zero_left_rhs_eq_iff.{1, 0}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    sA sB (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2))

example :
    ofPilotSeries.{0,1}
        (add
          sA
          (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))) =
      ofPilotSeries.{0,1} sB ↔
      ofPilotSeries.{0,1} sA = ofPilotSeries.{0,1} sB := by
  exact (@ofPilotSeries_add_mul_monomial_zero_right_rhs_eq_iff.{1, 0}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    sA sB 2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2))

example :
    evalOmega.{0,1}
        (ofPilotSeries.{0,1}
          (add
            (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))
            sA)) =
      evalOmega.{0,1} (ofPilotSeries.{0,1} sB) ↔
      evalOmega.{0,1} (ofPilotSeries.{0,1} sA) = evalOmega.{0,1} (ofPilotSeries.{0,1} sB) := by
  exact (@evalOmega_ofPilotSeries_add_mul_monomial_zero_left_lhs_eq_iff.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    evalOmega.{0,1}
        (ofPilotSeries.{0,1}
          (add
            (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))
            sA)) =
      evalOmega.{0,1} (ofPilotSeries.{0,1} sB) ↔
      evalOmega.{0,1} (ofPilotSeries.{0,1} sA) = evalOmega.{0,1} (ofPilotSeries.{0,1} sB) := by
  exact (@evalOmega_ofPilotSeries_add_mul_monomial_zero_right_lhs_eq_iff.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    evalOmega.{0,1}
        (ofPilotSeries.{0,1}
          (add
            sA
            (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2))))) =
      evalOmega.{0,1} (ofPilotSeries.{0,1} sB) ↔
      evalOmega.{0,1} (ofPilotSeries.{0,1} sA) = evalOmega.{0,1} (ofPilotSeries.{0,1} sB) := by
  exact (@evalOmega_ofPilotSeries_add_mul_monomial_zero_left_rhs_eq_iff.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    sA sB (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2))

example :
    evalOmega.{0,1}
        (ofPilotSeries.{0,1}
          (add
            sA
            (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2))))) =
      evalOmega.{0,1} (ofPilotSeries.{0,1} sB) ↔
      evalOmega.{0,1} (ofPilotSeries.{0,1} sA) = evalOmega.{0,1} (ofPilotSeries.{0,1} sB) := by
  exact (@evalOmega_ofPilotSeries_add_mul_monomial_zero_right_rhs_eq_iff.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    sA sB 2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2))

example :
    pilotEval.{0,1}
        (add
          (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))
          sA) =
      pilotEval.{0,1} sB ↔
      pilotEval.{0,1} sA = pilotEval.{0,1} sB := by
  exact (@pilotEval_add_mul_monomial_zero_left_lhs_eq_iff.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    pilotEval.{0,1}
        (add
          (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))
          sA) =
      pilotEval.{0,1} sB ↔
      pilotEval.{0,1} sA = pilotEval.{0,1} sB := by
  exact (@pilotEval_add_mul_monomial_zero_right_lhs_eq_iff.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    pilotEval.{0,1}
        (add
          sA
          (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))) =
      pilotEval.{0,1} sB ↔
      pilotEval.{0,1} sA = pilotEval.{0,1} sB := by
  exact (@pilotEval_add_mul_monomial_zero_left_rhs_eq_iff.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    sA sB (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2))

example :
    pilotEval.{0,1}
        (add
          sA
          (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))) =
      pilotEval.{0,1} sB ↔
      pilotEval.{0,1} sA = pilotEval.{0,1} sB := by
  exact (@pilotEval_add_mul_monomial_zero_right_rhs_eq_iff.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    sA sB 2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2))

example :
    ofPilotSeries.{0,1} sB =
      ofPilotSeries.{0,1}
        (add
          (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))
          sA) ↔
      ofPilotSeries.{0,1} sB = ofPilotSeries.{0,1} sA := by
  exact (@ofPilotSeries_add_mul_monomial_zero_left_lhs_eq_iff_left.{1, 0}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    ofPilotSeries.{0,1} sB =
      ofPilotSeries.{0,1}
        (add
          sA
          (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))) ↔
      ofPilotSeries.{0,1} sB = ofPilotSeries.{0,1} sA := by
  exact (@ofPilotSeries_add_mul_monomial_zero_right_rhs_eq_iff_left.{1, 0}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    sA sB 2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2))

example :
    evalOmega.{0,1} (ofPilotSeries.{0,1} sB) =
      evalOmega.{0,1}
        (ofPilotSeries.{0,1}
          (add
            (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))
            sA)) ↔
      evalOmega.{0,1} (ofPilotSeries.{0,1} sB) = evalOmega.{0,1} (ofPilotSeries.{0,1} sA) := by
  exact (@evalOmega_ofPilotSeries_add_mul_monomial_zero_left_lhs_eq_iff_left.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    evalOmega.{0,1} (ofPilotSeries.{0,1} sB) =
      evalOmega.{0,1}
        (ofPilotSeries.{0,1}
          (add
            sA
            (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2))))) ↔
      evalOmega.{0,1} (ofPilotSeries.{0,1} sB) = evalOmega.{0,1} (ofPilotSeries.{0,1} sA) := by
  exact (@evalOmega_ofPilotSeries_add_mul_monomial_zero_right_rhs_eq_iff_left.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    sA sB 2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2))

example :
    pilotEval.{0,1} sB =
      pilotEval.{0,1}
        (add
          (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))
          sA) ↔
      pilotEval.{0,1} sB = pilotEval.{0,1} sA := by
  exact (@pilotEval_add_mul_monomial_zero_left_lhs_eq_iff_left.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    pilotEval.{0,1} sB =
      pilotEval.{0,1}
        (add
          sA
          (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))) ↔
      pilotEval.{0,1} sB = pilotEval.{0,1} sA := by
  exact (@pilotEval_add_mul_monomial_zero_right_rhs_eq_iff_left.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    sA sB 2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2))

example :
    ofPilotSeries.{0,1} sB =
      ofPilotSeries.{0,1}
        (add
          (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))
          sA) ↔
      ofPilotSeries.{0,1} sB = ofPilotSeries.{0,1} sA := by
  exact (@ofPilotSeries_add_mul_monomial_zero_right_lhs_eq_iff_left.{1, 0}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    ofPilotSeries.{0,1} sB =
      ofPilotSeries.{0,1}
        (add
          sA
          (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))) ↔
      ofPilotSeries.{0,1} sB = ofPilotSeries.{0,1} sA := by
  exact (@ofPilotSeries_add_mul_monomial_zero_left_rhs_eq_iff_left.{1, 0}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    sA sB (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2))

example :
    evalOmega.{0,1} (ofPilotSeries.{0,1} sB) =
      evalOmega.{0,1}
        (ofPilotSeries.{0,1}
          (add
            (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))
            sA)) ↔
      evalOmega.{0,1} (ofPilotSeries.{0,1} sB) = evalOmega.{0,1} (ofPilotSeries.{0,1} sA) := by
  exact (@evalOmega_ofPilotSeries_add_mul_monomial_zero_right_lhs_eq_iff_left.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    evalOmega.{0,1} (ofPilotSeries.{0,1} sB) =
      evalOmega.{0,1}
        (ofPilotSeries.{0,1}
          (add
            sA
            (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2))))) ↔
      evalOmega.{0,1} (ofPilotSeries.{0,1} sB) = evalOmega.{0,1} (ofPilotSeries.{0,1} sA) := by
  exact (@evalOmega_ofPilotSeries_add_mul_monomial_zero_left_rhs_eq_iff_left.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    sA sB (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2))

example :
    pilotEval.{0,1} sB =
      pilotEval.{0,1}
        (add
          (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))
          sA) ↔
      pilotEval.{0,1} sB = pilotEval.{0,1} sA := by
  exact (@pilotEval_add_mul_monomial_zero_right_lhs_eq_iff_left.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    pilotEval.{0,1} sB =
      pilotEval.{0,1}
        (add
          sA
          (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))) ↔
      pilotEval.{0,1} sB = pilotEval.{0,1} sA := by
  exact (@pilotEval_add_mul_monomial_zero_left_rhs_eq_iff_left.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    sA sB (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2))

example :
    ofPilotSeries.{0,1}
        (add
          (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))
          sA) =
      ofPilotSeries.{0,1} sB ↔
      ofPilotSeries.{0,1} sB = ofPilotSeries.{0,1} sA := by
  exact (@ofPilotSeries_add_mul_monomial_zero_left_lhs_eq_iff_right.{1, 0}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    ofPilotSeries.{0,1}
        (add
          (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))
          sA) =
      ofPilotSeries.{0,1} sB ↔
      ofPilotSeries.{0,1} sB = ofPilotSeries.{0,1} sA := by
  exact (@ofPilotSeries_add_mul_monomial_zero_right_lhs_eq_iff_right.{1, 0}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    ofPilotSeries.{0,1}
        (add
          sA
          (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))) =
      ofPilotSeries.{0,1} sB ↔
      ofPilotSeries.{0,1} sB = ofPilotSeries.{0,1} sA := by
  exact (@ofPilotSeries_add_mul_monomial_zero_left_rhs_eq_iff_right.{1, 0}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    sA sB (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2))

example :
    ofPilotSeries.{0,1}
        (add
          sA
          (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))) =
      ofPilotSeries.{0,1} sB ↔
      ofPilotSeries.{0,1} sB = ofPilotSeries.{0,1} sA := by
  exact (@ofPilotSeries_add_mul_monomial_zero_right_rhs_eq_iff_right.{1, 0}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    sA sB 2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2))

example :
    evalOmega.{0,1}
        (ofPilotSeries.{0,1}
          (add
            (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))
            sA)) =
      evalOmega.{0,1} (ofPilotSeries.{0,1} sB) ↔
      evalOmega.{0,1} (ofPilotSeries.{0,1} sB) = evalOmega.{0,1} (ofPilotSeries.{0,1} sA) := by
  exact (@evalOmega_ofPilotSeries_add_mul_monomial_zero_left_lhs_eq_iff_right.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    evalOmega.{0,1}
        (ofPilotSeries.{0,1}
          (add
            (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))
            sA)) =
      evalOmega.{0,1} (ofPilotSeries.{0,1} sB) ↔
      evalOmega.{0,1} (ofPilotSeries.{0,1} sB) = evalOmega.{0,1} (ofPilotSeries.{0,1} sA) := by
  exact (@evalOmega_ofPilotSeries_add_mul_monomial_zero_right_lhs_eq_iff_right.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    evalOmega.{0,1}
        (ofPilotSeries.{0,1}
          (add
            sA
            (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2))))) =
      evalOmega.{0,1} (ofPilotSeries.{0,1} sB) ↔
      evalOmega.{0,1} (ofPilotSeries.{0,1} sB) = evalOmega.{0,1} (ofPilotSeries.{0,1} sA) := by
  exact (@evalOmega_ofPilotSeries_add_mul_monomial_zero_left_rhs_eq_iff_right.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    sA sB (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2))

example :
    evalOmega.{0,1}
        (ofPilotSeries.{0,1}
          (add
            sA
            (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2))))) =
      evalOmega.{0,1} (ofPilotSeries.{0,1} sB) ↔
      evalOmega.{0,1} (ofPilotSeries.{0,1} sB) = evalOmega.{0,1} (ofPilotSeries.{0,1} sA) := by
  exact (@evalOmega_ofPilotSeries_add_mul_monomial_zero_right_rhs_eq_iff_right.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    sA sB 2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2))

example :
    pilotEval.{0,1}
        (add
          (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))
          sA) =
      pilotEval.{0,1} sB ↔
      pilotEval.{0,1} sB = pilotEval.{0,1} sA := by
  exact (@pilotEval_add_mul_monomial_zero_left_lhs_eq_iff_right.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    pilotEval.{0,1}
        (add
          (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))
          sA) =
      pilotEval.{0,1} sB ↔
      pilotEval.{0,1} sB = pilotEval.{0,1} sA := by
  exact (@pilotEval_add_mul_monomial_zero_right_lhs_eq_iff_right.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2) sA sB)

example :
    pilotEval.{0,1}
        (add
          sA
          (mul (monomial 0 (OrdinalCNF.ofNat 1)) (monomial (-3) (OrdinalCNF.ofNat 2)))) =
      pilotEval.{0,1} sB ↔
      pilotEval.{0,1} sB = pilotEval.{0,1} sA := by
  exact (@pilotEval_add_mul_monomial_zero_left_rhs_eq_iff_right.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    sA sB (-3) (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2))

example :
    pilotEval.{0,1}
        (add
          sA
          (mul (monomial 2 (OrdinalCNF.ofNat 1)) (monomial 0 (OrdinalCNF.ofNat 2)))) =
      pilotEval.{0,1} sB ↔
      pilotEval.{0,1} sB = pilotEval.{0,1} sA := by
  exact (@pilotEval_add_mul_monomial_zero_right_rhs_eq_iff_right.{0, 1}
    (by infer_instance : HyperserialDescription.{1,1} Surreal.{0})
    sA sB 2 (OrdinalCNF.ofNat 1) (OrdinalCNF.ofNat 2))

example :
    evalOmega (ofPilotSeries (monomial 0 (OrdinalCNF.ofNat 7))) = 0 := by
  exact evalOmega_ofPilotSeries_monomial_zero (OrdinalCNF.ofNat 7)

example :
    ofPilotSeries (monomial 0 (OrdinalCNF.ofNat 7)) = 0 := by
  exact ofPilotSeries_monomial_zero (OrdinalCNF.ofNat 7)

example :
    pilotEval (monomial 0 (OrdinalCNF.ofNat 7)) = 0 := by
  exact pilotEval_monomial_zero (OrdinalCNF.ofNat 7)

example :
    pilotEval sA = sA.foldr (fun t acc => BridgePilot.termSem surrealModel t + acc) 0 := by
  simpa using (pilotEval_eq_foldr sA)

example : ∃! h : HSNo, evalOmega h = evalOmega (ofPilotSeries sA) := by
  simpa using (existsUnique_ofPilotSeries sA)
end Numbers
end Tests
end HeytingLean
