import HeytingLean.LeanCP.VCG.SWPSound
import HeytingLean.LeanCP.Bench.Meta

namespace HeytingLean.LeanCP.Bench.ScalarArithmetic

open HeytingLean.LeanCP
open HeytingLean.LeanCP.Bench

set_option linter.unnecessarySimpa false

def add1Body : CStmt :=
  .ret (.binop .add (.var "x") (.intLit 1))

def add1Spec (x : Int) : SFunSpec where
  name := "bench_add1"
  params := [("x", .int)]
  retType := .int
  pre := fun st => st.lookupVar "x" = some (.int x)
  post := fun ret _ => ret = .int (x + 1)
  body := add1Body

theorem add1_correct (x : Int) : sgenVC (add1Spec x) := by
  intro st hx
  have hEvalX : evalExpr (.var "x") st = some (.int x) := by
    simpa [evalExpr] using hx
  have hStatic :
      evalStaticExpr (.binop .add (.var "x") (.intLit 1)) = none := by
    simp [evalStaticExpr]
  have hEval :
      evalExpr (.binop .add (.var "x") (.intLit 1)) st = some (.int (x + 1)) := by
    simp [evalExpr, evalStaticExpr, hStatic, hEvalX]
  change swp add1Body (add1Spec x).post st
  simpa [add1Body, swp, add1Spec, hEval]

def sub1Body : CStmt :=
  .ret (.binop .sub (.var "x") (.intLit 1))

def sub1Spec (x : Int) : SFunSpec where
  name := "bench_sub1"
  params := [("x", .int)]
  retType := .int
  pre := fun st => st.lookupVar "x" = some (.int x)
  post := fun ret _ => ret = .int (x - 1)
  body := sub1Body

theorem sub1_correct (x : Int) : sgenVC (sub1Spec x) := by
  intro st hx
  have hEvalX : evalExpr (.var "x") st = some (.int x) := by
    simpa [evalExpr] using hx
  have hStatic :
      evalStaticExpr (.binop .sub (.var "x") (.intLit 1)) = none := by
    simp [evalStaticExpr]
  have hEval :
      evalExpr (.binop .sub (.var "x") (.intLit 1)) st = some (.int (x - 1)) := by
    simp [evalExpr, evalStaticExpr, hStatic, hEvalX]
  change swp sub1Body (sub1Spec x).post st
  simpa [sub1Body, swp, sub1Spec, hEval]

def doubleBody : CStmt :=
  .ret (.binop .add (.var "x") (.var "x"))

def doubleSpec (x : Int) : SFunSpec where
  name := "bench_double"
  params := [("x", .int)]
  retType := .int
  pre := fun st => st.lookupVar "x" = some (.int x)
  post := fun ret _ => ret = .int (x + x)
  body := doubleBody

theorem double_correct (x : Int) : sgenVC (doubleSpec x) := by
  intro st hx
  have hEvalX : evalExpr (.var "x") st = some (.int x) := by
    simpa [evalExpr] using hx
  have hStatic :
      evalStaticExpr (.binop .add (.var "x") (.var "x")) = none := by
    simp [evalStaticExpr]
  have hEval :
      evalExpr (.binop .add (.var "x") (.var "x")) st = some (.int (x + x)) := by
    simp [evalExpr, hStatic, hEvalX, evalBinOp_add_int_int]
  change swp doubleBody (doubleSpec x).post st
  simpa [doubleBody, swp, doubleSpec, hEval]

def min2Body : CStmt :=
  .ite (.binop .gt (.var "a") (.var "b"))
    (.ret (.var "b"))
    (.ret (.var "a"))

def min2Spec (a b : Int) : SFunSpec where
  name := "bench_min2"
  params := [("a", .int), ("b", .int)]
  retType := .int
  pre := fun st =>
    st.lookupVar "a" = some (.int a) ∧
    st.lookupVar "b" = some (.int b)
  post := fun ret _ => ret = .int (if a > b then b else a)
  body := min2Body

theorem min2_correct (a b : Int) : sgenVC (min2Spec a b) := by
  intro st hpre
  rcases hpre with ⟨ha, hb⟩
  have hEvalA : evalExpr (.var "a") st = some (.int a) := by
    simpa [evalExpr] using ha
  have hEvalB : evalExpr (.var "b") st = some (.int b) := by
    simpa [evalExpr] using hb
  by_cases hgt : a > b
  · have hCond :
        evalExpr (.binop .gt (.var "a") (.var "b")) st = some (.int 1) := by
      simp [evalExpr, evalStaticExpr, hEvalA, hEvalB, evalBinOp_gt_int_int, hgt]
    change swp min2Body (min2Spec a b).post st
    simpa [min2Body, swp, min2Spec, hCond, isTruthy, hEvalB, hgt]
  · have hCond :
        evalExpr (.binop .gt (.var "a") (.var "b")) st = some (.int 0) := by
      simp [evalExpr, evalStaticExpr, hEvalA, hEvalB, evalBinOp_gt_int_int, hgt]
    change swp min2Body (min2Spec a b).post st
    simpa [min2Body, swp, min2Spec, hCond, isTruthy, hEvalA, hgt]

def absBody : CStmt :=
  .ite (.binop .gt (.var "x") (.intLit (-1)))
    (.ret (.var "x"))
    (.ret (.binop .sub (.intLit 0) (.var "x")))

def absSpec (x : Int) : SFunSpec where
  name := "bench_abs"
  params := [("x", .int)]
  retType := .int
  pre := fun st => st.lookupVar "x" = some (.int x)
  post := fun ret _ => ret = .int (if x > -1 then x else 0 - x)
  body := absBody

theorem abs_correct (x : Int) : sgenVC (absSpec x) := by
  intro st hx
  have hEvalX : evalExpr (.var "x") st = some (.int x) := by
    simpa [evalExpr] using hx
  by_cases hgt : x > -1
  · have hCond :
        evalExpr (.binop .gt (.var "x") (.intLit (-1))) st = some (.int 1) := by
      simp [evalExpr, evalStaticExpr, hEvalX, evalBinOp_gt_int_int, hgt]
    change swp absBody (absSpec x).post st
    simpa [absBody, swp, absSpec, hCond, isTruthy, hEvalX, hgt]
  · have hCond :
        evalExpr (.binop .gt (.var "x") (.intLit (-1))) st = some (.int 0) := by
      simp [evalExpr, evalStaticExpr, hEvalX, evalBinOp_gt_int_int, hgt]
    have hStatic :
        evalStaticExpr (.binop .sub (.intLit 0) (.var "x")) = none := by
      simp [evalStaticExpr]
    have hEvalNeg :
        evalExpr (.binop .sub (.intLit 0) (.var "x")) st = some (.int (0 - x)) := by
      simp [evalExpr, evalStaticExpr, hStatic, hEvalX]
    change swp absBody (absSpec x).post st
    simpa [absBody, swp, absSpec, hCond, isTruthy, hEvalNeg, hgt]

def clampNonnegBody : CStmt :=
  .ite (.binop .gt (.var "x") (.intLit 0))
    (.ret (.var "x"))
    (.ret (.intLit 0))

def clampNonnegSpec (x : Int) : SFunSpec where
  name := "bench_clamp_nonneg"
  params := [("x", .int)]
  retType := .int
  pre := fun st => st.lookupVar "x" = some (.int x)
  post := fun ret _ => ret = .int (if x > 0 then x else 0)
  body := clampNonnegBody

theorem clampNonneg_correct (x : Int) : sgenVC (clampNonnegSpec x) := by
  intro st hx
  have hEvalX : evalExpr (.var "x") st = some (.int x) := by
    simpa [evalExpr] using hx
  by_cases hgt : x > 0
  · have hCond :
        evalExpr (.binop .gt (.var "x") (.intLit 0)) st = some (.int 1) := by
      simp [evalExpr, evalStaticExpr, hEvalX, evalBinOp_gt_int_int, hgt]
    change swp clampNonnegBody (clampNonnegSpec x).post st
    simpa [clampNonnegBody, swp, clampNonnegSpec, hCond, isTruthy, hEvalX, hgt]
  · have hCond :
        evalExpr (.binop .gt (.var "x") (.intLit 0)) st = some (.int 0) := by
      simp [evalExpr, evalStaticExpr, hEvalX, evalBinOp_gt_int_int, hgt]
    change swp clampNonnegBody (clampNonnegSpec x).post st
    simp [clampNonnegBody, swp, clampNonnegSpec, hCond, isTruthy, hgt, evalExpr, evalStaticExpr]

def scalarEntries : List BenchEntry :=
  [ { id := "bench_add1"
    , domain := .scalarArith
    , moduleName := "HeytingLean.LeanCP.Bench.ScalarArithmetic"
    , theoremDecl := (``HeytingLean.LeanCP.Bench.ScalarArithmetic.add1_correct : Lean.Name)
    , programDecl := (``HeytingLean.LeanCP.Bench.ScalarArithmetic.add1Body : Lean.Name)
    , entryKind := "topLevel"
    , proofKind := .symbolic
    , generality := .parametric
    , usesAnnotations := false
    , countsTowardPhase8 := true }
  , { id := "bench_sub1"
    , domain := .scalarArith
    , moduleName := "HeytingLean.LeanCP.Bench.ScalarArithmetic"
    , theoremDecl := (``HeytingLean.LeanCP.Bench.ScalarArithmetic.sub1_correct : Lean.Name)
    , programDecl := (``HeytingLean.LeanCP.Bench.ScalarArithmetic.sub1Body : Lean.Name)
    , entryKind := "topLevel"
    , proofKind := .symbolic
    , generality := .parametric
    , usesAnnotations := false
    , countsTowardPhase8 := true }
  , { id := "bench_double"
    , domain := .scalarArith
    , moduleName := "HeytingLean.LeanCP.Bench.ScalarArithmetic"
    , theoremDecl := (``HeytingLean.LeanCP.Bench.ScalarArithmetic.double_correct : Lean.Name)
    , programDecl := (``HeytingLean.LeanCP.Bench.ScalarArithmetic.doubleBody : Lean.Name)
    , entryKind := "topLevel"
    , proofKind := .symbolic
    , generality := .parametric
    , usesAnnotations := false
    , countsTowardPhase8 := true }
  , { id := "bench_min2"
    , domain := .scalarArith
    , moduleName := "HeytingLean.LeanCP.Bench.ScalarArithmetic"
    , theoremDecl := (``HeytingLean.LeanCP.Bench.ScalarArithmetic.min2_correct : Lean.Name)
    , programDecl := (``HeytingLean.LeanCP.Bench.ScalarArithmetic.min2Body : Lean.Name)
    , entryKind := "topLevel"
    , proofKind := .symbolic
    , generality := .parametric
    , usesAnnotations := false
    , countsTowardPhase8 := true }
  , { id := "bench_abs"
    , domain := .scalarArith
    , moduleName := "HeytingLean.LeanCP.Bench.ScalarArithmetic"
    , theoremDecl := (``HeytingLean.LeanCP.Bench.ScalarArithmetic.abs_correct : Lean.Name)
    , programDecl := (``HeytingLean.LeanCP.Bench.ScalarArithmetic.absBody : Lean.Name)
    , entryKind := "topLevel"
    , proofKind := .symbolic
    , generality := .parametric
    , usesAnnotations := false
    , countsTowardPhase8 := true }
  , { id := "bench_clamp_nonneg"
    , domain := .scalarArith
    , moduleName := "HeytingLean.LeanCP.Bench.ScalarArithmetic"
    , theoremDecl := (``HeytingLean.LeanCP.Bench.ScalarArithmetic.clampNonneg_correct : Lean.Name)
    , programDecl := (``HeytingLean.LeanCP.Bench.ScalarArithmetic.clampNonnegBody : Lean.Name)
    , entryKind := "topLevel"
    , proofKind := .symbolic
    , generality := .parametric
    , usesAnnotations := false
    , countsTowardPhase8 := true } ]

end HeytingLean.LeanCP.Bench.ScalarArithmetic
