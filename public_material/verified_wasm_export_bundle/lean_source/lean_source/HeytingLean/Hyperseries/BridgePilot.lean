import HeytingLean.Hyperseries.DSL
import HeytingLean.Hyperseries.Eval
import HeytingLean.Numbers.Ordinal.Notation
import HeytingLean.Numbers.Surreal.Hyperseries

namespace HeytingLean
namespace Hyperseries
namespace BridgePilot

noncomputable section

open HeytingLean.Numbers.Ordinal
open HeytingLean.Numbers.Surreal.Hyperseries

/-- Encode a pilot exponent as a syntactic hyper-exponential over `X` (integer lane). -/
def expExpr (e : OrdinalCNF) : HExpr :=
  ExprC.hyperExp (NONote.repr e) (ExprC.X : HExpr)

/-- Translate a pilot term into the integer-coefficient DSL. -/
def ofTerm (t : Term) : HExpr :=
  ExprC.mul (ExprC.C t.coeff) (expExpr t.exp)

/-- Tail-recursive helper for translating pilot series to DSL expressions. -/
def ofSeriesWith (tail : HExpr) : Series → HExpr
  | [] => tail
  | t :: ts => ExprC.add (ofTerm t) (ofSeriesWith tail ts)

/-- Translate a pilot series into the integer-coefficient DSL. -/
def ofSeries (s : Series) : HExpr :=
  ofSeriesWith (ExprC.C 0) s

@[simp] theorem ofSeriesWith_nil (tail : HExpr) : ofSeriesWith tail [] = tail := rfl

@[simp] theorem ofSeriesWith_cons (tail : HExpr) (t : Term) (ts : Series) :
    ofSeriesWith tail (t :: ts) = ExprC.add (ofTerm t) (ofSeriesWith tail ts) := rfl

@[simp] theorem ofSeries_nil : ofSeries [] = ExprC.C (0 : ℤ) := rfl

@[simp] theorem ofSeriesWith_append (tail : HExpr) (x y : Series) :
    ofSeriesWith tail (x ++ y) = ofSeriesWith (ofSeriesWith tail y) x := by
  induction x with
  | nil =>
      simp [ofSeriesWith]
  | cons t ts ih =>
      simp [ofSeriesWith, ih]

@[simp] theorem ofSeries_add (x y : Series) :
    ofSeries (add x y) = ofSeriesWith (ofSeries y) x := by
  simp [add, ofSeries, ofSeriesWith_append]

theorem ofSeries_mul_monomial (c₁ c₂ : Int) (e₁ e₂ : OrdinalCNF) :
    ofSeries (mul (monomial c₁ e₁) (monomial c₂ e₂)) =
      ofSeries (monomial (c₁ * c₂) (e₁ + e₂)) := by
  exact congrArg ofSeries (mul_monomial c₁ c₂ e₁ e₂)

/-- Encode a pilot exponent as a syntactic hyper-exponential over `X` (rational lane). -/
def expExprQ (e : OrdinalCNF) : HExprQ :=
  ExprC.hyperExp (NONote.repr e) (ExprC.X : HExprQ)

/-- Translate a pilot term into the rational-coefficient DSL. -/
def ofTermQ (t : Term) : HExprQ :=
  ExprC.mul (ExprC.C ((t.coeff : Int) : Rat)) (expExprQ t.exp)

/-- Tail-recursive helper for translating pilot series to rational DSL expressions. -/
def ofSeriesQWith (tail : HExprQ) : Series → HExprQ
  | [] => tail
  | t :: ts => ExprC.add (ofTermQ t) (ofSeriesQWith tail ts)

/-- Translate a pilot series into the rational-coefficient DSL. -/
def ofSeriesQ (s : Series) : HExprQ :=
  ofSeriesQWith (ExprC.C 0) s

@[simp] theorem ofSeriesQWith_nil (tail : HExprQ) : ofSeriesQWith tail [] = tail := rfl

@[simp] theorem ofSeriesQWith_cons (tail : HExprQ) (t : Term) (ts : Series) :
    ofSeriesQWith tail (t :: ts) = ExprC.add (ofTermQ t) (ofSeriesQWith tail ts) := rfl

@[simp] theorem ofSeriesQ_nil : ofSeriesQ [] = ExprC.C (0 : Rat) := rfl

@[simp] theorem ofSeriesQWith_append (tail : HExprQ) (x y : Series) :
    ofSeriesQWith tail (x ++ y) = ofSeriesQWith (ofSeriesQWith tail y) x := by
  induction x with
  | nil =>
      simp [ofSeriesQWith]
  | cons t ts ih =>
      simp [ofSeriesQWith, ih]

@[simp] theorem ofSeriesQ_add (x y : Series) :
    ofSeriesQ (add x y) = ofSeriesQWith (ofSeriesQ y) x := by
  simp [add, ofSeriesQ, ofSeriesQWith_append]

theorem ofSeriesQ_mul_monomial (c₁ c₂ : Int) (e₁ e₂ : OrdinalCNF) :
    ofSeriesQ (mul (monomial c₁ e₁) (monomial c₂ e₂)) =
      ofSeriesQ (monomial (c₁ * c₂) (e₁ + e₂)) := by
  exact congrArg ofSeriesQ (mul_monomial c₁ c₂ e₁ e₂)

/-- Lift integer-coefficient expressions to rational-coefficient expressions. -/
def liftIntToRat : HExpr → HExprQ
  | ExprC.C z => ExprC.C (z : Rat)
  | ExprC.X => ExprC.X
  | ExprC.add a b => ExprC.add (liftIntToRat a) (liftIntToRat b)
  | ExprC.mul a b => ExprC.mul (liftIntToRat a) (liftIntToRat b)
  | ExprC.neg a => ExprC.neg (liftIntToRat a)
  | ExprC.exp a => ExprC.exp (liftIntToRat a)
  | ExprC.log a => ExprC.log (liftIntToRat a)
  | ExprC.hyperExp α a => ExprC.hyperExp α (liftIntToRat a)
  | ExprC.hyperLog α a => ExprC.hyperLog α (liftIntToRat a)

@[simp] theorem liftIntToRat_C (z : Int) :
    liftIntToRat (ExprC.C z) = ExprC.C (z : Rat) := rfl

@[simp] theorem liftIntToRat_X :
    liftIntToRat (ExprC.X : HExpr) = (ExprC.X : HExprQ) := rfl

@[simp] theorem liftIntToRat_expExpr (e : OrdinalCNF) :
    liftIntToRat (expExpr e) = expExprQ e := by
  simp [expExpr, expExprQ, liftIntToRat]

@[simp] theorem liftIntToRat_ofTerm (t : Term) :
    liftIntToRat (ofTerm t) = ofTermQ t := by
  simp [ofTerm, ofTermQ, liftIntToRat]

@[simp] theorem liftIntToRat_ofSeriesWith (tail : HExpr) (s : Series) :
    liftIntToRat (ofSeriesWith tail s) = ofSeriesQWith (liftIntToRat tail) s := by
  induction s with
  | nil =>
      simp [ofSeriesWith, ofSeriesQWith]
  | cons t ts ih =>
      simp [ofSeriesWith, ofSeriesQWith, liftIntToRat, ih]

@[simp] theorem liftIntToRat_ofSeries (s : Series) :
    liftIntToRat (ofSeries s) = ofSeriesQ s := by
  simp [ofSeries, ofSeriesQ, liftIntToRat_ofSeriesWith]

section LiftEval

variable {K : Type*} [Field K] (M : HyperserialModel K)

@[simp] theorem eval_liftIntToRat (e : HExpr) :
    HExprQ.eval M (liftIntToRat e) = HExpr.eval M e := by
  induction e with
  | C z =>
      simp [liftIntToRat]
  | X =>
      simp [liftIntToRat]
  | add a b ihA ihB =>
      simp [liftIntToRat, ihA, ihB]
  | mul a b ihA ihB =>
      simp [liftIntToRat, ihA, ihB]
  | neg a ih =>
      simp [liftIntToRat, ih]
  | exp a ih =>
      simpa [HExpr.eval, HExprQ.eval, liftIntToRat] using congrArg M.exp ih
  | log a ih =>
      simpa [HExpr.eval, HExprQ.eval, liftIntToRat] using congrArg M.log ih
  | hyperExp α a ih =>
      simpa [HExpr.eval, HExprQ.eval, liftIntToRat] using congrArg (M.hyperExp α) ih
  | hyperLog α a ih =>
      simpa [HExpr.eval, HExprQ.eval, liftIntToRat] using congrArg (M.hyperLog α) ih

@[simp] theorem eval_ofSeriesQ_eq_eval_ofSeries (s : Series) :
    HExprQ.eval M (ofSeriesQ s) = HExpr.eval M (ofSeries s) := by
  rw [← liftIntToRat_ofSeries (s := s)]
  exact eval_liftIntToRat (M := M) (ofSeries s)

end LiftEval

section SemanticsZ

variable {K : Type*} [CommRing K] (M : HyperserialModel K)

/-- Semantics of one pilot term under the integer-lane expression translation. -/
def termSem (t : Term) : K :=
  (t.coeff : K) * HExpr.eval M (expExpr t.exp)

/-- Semantics of pilot series with a tail accumulator. -/
def seriesSemWith (tail : K) : Series → K
  | [] => tail
  | t :: ts => termSem M t + seriesSemWith tail ts

/-- Semantics of pilot series in the integer lane. -/
def seriesSem (s : Series) : K :=
  seriesSemWith M 0 s

@[simp] theorem eval_expExpr (e : OrdinalCNF) :
    HExpr.eval M (expExpr e) = M.hyperExp (NONote.repr e) M.omega := by
  rfl

@[simp] theorem eval_ofTerm (t : Term) :
    HExpr.eval M (ofTerm t) = termSem M t := by
  simp [ofTerm, termSem]

@[simp] theorem eval_ofSeriesWith (tail : HExpr) (s : Series) :
    HExpr.eval M (ofSeriesWith tail s) = seriesSemWith M (HExpr.eval M tail) s := by
  induction s with
  | nil =>
      simp [ofSeriesWith, seriesSemWith]
  | cons t ts ih =>
      simp [ofSeriesWith, seriesSemWith, ih, termSem]

@[simp] theorem eval_ofSeries (s : Series) :
    HExpr.eval M (ofSeries s) = seriesSem M s := by
  simp [ofSeries, seriesSem]

@[simp] theorem seriesSem_nil :
    seriesSem M [] = (0 : K) := by
  rfl

theorem seriesSem_eq_foldr (s : Series) :
    seriesSem M s = s.foldr (fun t acc => termSem M t + acc) 0 := by
  induction s with
  | nil =>
      rfl
  | cons t ts ih =>
      simp [seriesSem, seriesSemWith]
      rw [show seriesSemWith M 0 ts = seriesSem M ts by rfl]
      exact ih

@[simp] theorem seriesSem_monomial (c : Int) (e : OrdinalCNF) :
    seriesSem M (monomial c e) = (c : K) * M.hyperExp (NONote.repr e) M.omega := by
  simp [seriesSem, seriesSemWith, termSem, monomial, eval_expExpr]

@[simp] theorem eval_ofSeries_monomial (c : Int) (e : OrdinalCNF) :
    HExpr.eval M (ofSeries (monomial c e)) = (c : K) * M.hyperExp (NONote.repr e) M.omega := by
  rw [eval_ofSeries]
  exact seriesSem_monomial (M := M) c e

theorem eval_ofSeries_eq_foldr (s : Series) :
    HExpr.eval M (ofSeries s) = s.foldr (fun t acc => termSem M t + acc) 0 := by
  rw [eval_ofSeries, seriesSem_eq_foldr]

theorem seriesSemWith_append (tail : K) (x y : Series) :
    seriesSemWith M tail (x ++ y) = seriesSemWith M (seriesSemWith M tail y) x := by
  induction x with
  | nil =>
      simp [seriesSemWith]
  | cons t ts ih =>
      simp [seriesSemWith, ih]

theorem seriesSemWith_eq_add (tail : K) (s : Series) :
    seriesSemWith M tail s = seriesSem M s + tail := by
  induction s with
  | nil =>
      simp [seriesSemWith, seriesSem]
  | cons t ts ih =>
      simp [seriesSemWith, seriesSem, ih, add_assoc]

@[simp] theorem seriesSem_add (x y : Series) :
    seriesSem M (add x y) = seriesSem M x + seriesSem M y := by
  rw [show add x y = x ++ y by rfl]
  unfold seriesSem
  rw [seriesSemWith_append]
  rw [seriesSemWith_eq_add (M := M) (tail := seriesSemWith M 0 y) (s := x)]
  rw [show seriesSemWith M 0 y = seriesSem M y by rfl]
  simp [seriesSem]

@[simp] theorem eval_ofSeries_add (x y : Series) :
    HExpr.eval M (ofSeries (add x y)) = seriesSem M x + seriesSem M y := by
  exact Eq.trans (eval_ofSeries (M := M) (add x y)) (seriesSem_add (M := M) x y)

theorem seriesSemWith_normalize (tail : K) (s : Series) :
    seriesSemWith M tail (normalize s) = seriesSemWith M tail s := by
  induction s with
  | nil =>
      simp [normalize, seriesSemWith]
  | cons t ts ih =>
      by_cases h : t.coeff ≠ 0
      · calc
          seriesSemWith M tail (normalize (t :: ts))
              = termSem M t + seriesSemWith M tail (normalize ts) := by
                simp [normalize, seriesSemWith, h]
          _ = termSem M t + seriesSemWith M tail ts := by rw [ih]
          _ = seriesSemWith M tail (t :: ts) := by simp [seriesSemWith]
      · have h0 : t.coeff = 0 := by simpa using h
        calc
          seriesSemWith M tail (normalize (t :: ts))
              = seriesSemWith M tail (normalize ts) := by
                simp [normalize, h]
          _ = seriesSemWith M tail ts := ih
          _ = seriesSemWith M tail (t :: ts) := by
                simp [seriesSemWith, termSem, h0]

@[simp] theorem seriesSem_normalize (s : Series) :
    seriesSem M (normalize s) = seriesSem M s := by
  show seriesSemWith M 0 (normalize s) = seriesSemWith M 0 s
  exact seriesSemWith_normalize (M := M) (tail := (0 : K)) s

@[simp] theorem eval_ofSeries_normalize (s : Series) :
    HExpr.eval M (ofSeries (normalize s)) = HExpr.eval M (ofSeries s) := by
  rw [eval_ofSeries, eval_ofSeries, seriesSem_normalize]

@[simp] theorem eval_ofSeries_mul_monomial (c₁ c₂ : Int) (e₁ e₂ : OrdinalCNF) :
    HExpr.eval M (ofSeries (mul (monomial c₁ e₁) (monomial c₂ e₂))) =
      HExpr.eval M (ofSeries (monomial (c₁ * c₂) (e₁ + e₂))) := by
  exact congrArg (HExpr.eval M) (ofSeries_mul_monomial c₁ c₂ e₁ e₂)

end SemanticsZ

section SemanticsQ

variable {K : Type*} [Field K] (M : HyperserialModel K)

/-- Semantics of one pilot term under the rational-lane expression translation. -/
def termSemQ (t : Term) : K :=
  ((t.coeff : Int) : K) * HExprQ.eval M (expExprQ t.exp)

/-- Semantics of pilot series with a tail accumulator in the rational lane. -/
def seriesSemQWith (tail : K) : Series → K
  | [] => tail
  | t :: ts => termSemQ M t + seriesSemQWith tail ts

/-- Semantics of pilot series in the rational lane. -/
def seriesSemQ (s : Series) : K :=
  seriesSemQWith M 0 s

@[simp] theorem eval_expExprQ (e : OrdinalCNF) :
    HExprQ.eval M (expExprQ e) = M.hyperExp (NONote.repr e) M.omega := by
  rfl

@[simp] theorem eval_ofTermQ (t : Term) :
    HExprQ.eval M (ofTermQ t) = termSemQ M t := by
  simp [ofTermQ, termSemQ]

@[simp] theorem eval_ofSeriesQWith (tail : HExprQ) (s : Series) :
    HExprQ.eval M (ofSeriesQWith tail s) = seriesSemQWith M (HExprQ.eval M tail) s := by
  induction s with
  | nil =>
      simp [ofSeriesQWith, seriesSemQWith]
  | cons t ts ih =>
      simp [ofSeriesQWith, seriesSemQWith, ih, termSemQ]

@[simp] theorem eval_ofSeriesQ (s : Series) :
    HExprQ.eval M (ofSeriesQ s) = seriesSemQ M s := by
  simp [ofSeriesQ, seriesSemQ]

@[simp] theorem seriesSemQ_nil :
    seriesSemQ M [] = (0 : K) := by
  rfl

theorem seriesSemQ_eq_foldr (s : Series) :
    seriesSemQ M s = s.foldr (fun t acc => termSemQ M t + acc) 0 := by
  induction s with
  | nil =>
      rfl
  | cons t ts ih =>
      simp [seriesSemQ, seriesSemQWith]
      rw [show seriesSemQWith M 0 ts = seriesSemQ M ts by rfl]
      exact ih

@[simp] theorem seriesSemQ_monomial (c : Int) (e : OrdinalCNF) :
    seriesSemQ M (monomial c e) = ((c : Int) : K) * M.hyperExp (NONote.repr e) M.omega := by
  simp [seriesSemQ, seriesSemQWith, termSemQ, monomial, eval_expExprQ]

@[simp] theorem eval_ofSeriesQ_monomial (c : Int) (e : OrdinalCNF) :
    HExprQ.eval M (ofSeriesQ (monomial c e)) = ((c : Int) : K) * M.hyperExp (NONote.repr e) M.omega := by
  rw [eval_ofSeriesQ]
  exact seriesSemQ_monomial (M := M) c e

theorem eval_ofSeriesQ_eq_foldr (s : Series) :
    HExprQ.eval M (ofSeriesQ s) = s.foldr (fun t acc => termSemQ M t + acc) 0 := by
  rw [eval_ofSeriesQ, seriesSemQ_eq_foldr]

theorem seriesSemQWith_append (tail : K) (x y : Series) :
    seriesSemQWith M tail (x ++ y) = seriesSemQWith M (seriesSemQWith M tail y) x := by
  induction x with
  | nil =>
      simp [seriesSemQWith]
  | cons t ts ih =>
      simp [seriesSemQWith, ih]

theorem seriesSemQWith_eq_add (tail : K) (s : Series) :
    seriesSemQWith M tail s = seriesSemQ M s + tail := by
  induction s with
  | nil =>
      simp [seriesSemQWith, seriesSemQ]
  | cons t ts ih =>
      simp [seriesSemQWith, seriesSemQ, ih, add_assoc]

@[simp] theorem seriesSemQ_add (x y : Series) :
    seriesSemQ M (add x y) = seriesSemQ M x + seriesSemQ M y := by
  rw [show add x y = x ++ y by rfl]
  unfold seriesSemQ
  rw [seriesSemQWith_append]
  rw [seriesSemQWith_eq_add (M := M) (tail := seriesSemQWith M 0 y) (s := x)]
  rw [show seriesSemQWith M 0 y = seriesSemQ M y by rfl]
  simp [seriesSemQ]

@[simp] theorem eval_ofSeriesQ_add (x y : Series) :
    HExprQ.eval M (ofSeriesQ (add x y)) = seriesSemQ M x + seriesSemQ M y := by
  exact Eq.trans (eval_ofSeriesQ (M := M) (add x y)) (seriesSemQ_add (M := M) x y)

theorem seriesSemQWith_normalize (tail : K) (s : Series) :
    seriesSemQWith M tail (normalize s) = seriesSemQWith M tail s := by
  induction s with
  | nil =>
      simp [normalize, seriesSemQWith]
  | cons t ts ih =>
      by_cases h : t.coeff ≠ 0
      · calc
          seriesSemQWith M tail (normalize (t :: ts))
              = termSemQ M t + seriesSemQWith M tail (normalize ts) := by
                simp [normalize, seriesSemQWith, h]
          _ = termSemQ M t + seriesSemQWith M tail ts := by rw [ih]
          _ = seriesSemQWith M tail (t :: ts) := by simp [seriesSemQWith]
      · have h0 : t.coeff = 0 := by simpa using h
        calc
          seriesSemQWith M tail (normalize (t :: ts))
              = seriesSemQWith M tail (normalize ts) := by
                simp [normalize, h]
          _ = seriesSemQWith M tail ts := ih
          _ = seriesSemQWith M tail (t :: ts) := by
                simp [seriesSemQWith, termSemQ, h0]

@[simp] theorem seriesSemQ_normalize (s : Series) :
    seriesSemQ M (normalize s) = seriesSemQ M s := by
  show seriesSemQWith M 0 (normalize s) = seriesSemQWith M 0 s
  exact seriesSemQWith_normalize (M := M) (tail := (0 : K)) s

@[simp] theorem eval_ofSeriesQ_normalize (s : Series) :
    HExprQ.eval M (ofSeriesQ (normalize s)) = HExprQ.eval M (ofSeriesQ s) := by
  rw [eval_ofSeriesQ, eval_ofSeriesQ, seriesSemQ_normalize]

@[simp] theorem eval_ofSeriesQ_mul_monomial (c₁ c₂ : Int) (e₁ e₂ : OrdinalCNF) :
    HExprQ.eval M (ofSeriesQ (mul (monomial c₁ e₁) (monomial c₂ e₂))) =
      HExprQ.eval M (ofSeriesQ (monomial (c₁ * c₂) (e₁ + e₂))) := by
  exact congrArg (HExprQ.eval M) (ofSeriesQ_mul_monomial c₁ c₂ e₁ e₂)

end SemanticsQ

section PublicAPI

variable {K : Type*} [CommRing K] (M : HyperserialModel K)

/-- Public API: evaluating translated pilot zero yields ring zero (integer lane). -/
@[simp] theorem eval_ofPilot_zero :
    HExpr.eval M (ofSeries ([] : Series)) = (0 : K) := by
  simp

/-- Public API: evaluating translated pilot monomials in the integer lane. -/
@[simp] theorem eval_ofPilot_monomial (c : Int) (e : OrdinalCNF) :
    HExpr.eval M (ofSeries (monomial c e)) = (c : K) * M.hyperExp (NONote.repr e) M.omega := by
  exact eval_ofSeries_monomial (M := M) c e

/-- Public API: translated pilot append is additive under evaluation (integer lane). -/
@[simp] theorem eval_ofPilot_append (x y : Series) :
    HExpr.eval M (ofSeries (x ++ y)) =
      HExpr.eval M (ofSeries x) + HExpr.eval M (ofSeries y) := by
  simpa [add] using (eval_ofSeries_add (M := M) x y)

/-- Public API: normalization is evaluation-invariant in the integer lane. -/
@[simp] theorem eval_ofPilot_normalize (s : Series) :
    HExpr.eval M (ofSeries (normalize s)) = HExpr.eval M (ofSeries s) := by
  exact eval_ofSeries_normalize (M := M) s

end PublicAPI

section PublicAPIQ

variable {K : Type*} [Field K] (M : HyperserialModel K)

/-- Public API: evaluating translated pilot zero yields ring zero (rational lane). -/
@[simp] theorem eval_ofPilotQ_zero :
    HExprQ.eval M (ofSeriesQ ([] : Series)) = (0 : K) := by
  simp

/-- Public API: evaluating translated pilot monomials in the rational lane. -/
@[simp] theorem eval_ofPilotQ_monomial (c : Int) (e : OrdinalCNF) :
    HExprQ.eval M (ofSeriesQ (monomial c e)) = ((c : Int) : K) * M.hyperExp (NONote.repr e) M.omega := by
  exact eval_ofSeriesQ_monomial (M := M) c e

/-- Public API: translated pilot append is additive under evaluation (rational lane). -/
@[simp] theorem eval_ofPilotQ_append (x y : Series) :
    HExprQ.eval M (ofSeriesQ (x ++ y)) =
      HExprQ.eval M (ofSeriesQ x) + HExprQ.eval M (ofSeriesQ y) := by
  calc
    HExprQ.eval M (ofSeriesQ (x ++ y)) = seriesSemQ M (x ++ y) := eval_ofSeriesQ (M := M) (x ++ y)
    _ = seriesSemQ M x + seriesSemQ M y := by simpa [add] using (seriesSemQ_add (M := M) x y)
    _ = HExprQ.eval M (ofSeriesQ x) + HExprQ.eval M (ofSeriesQ y) := by
      rw [eval_ofSeriesQ (M := M) x, eval_ofSeriesQ (M := M) y]

/-- Public API: normalization is evaluation-invariant in the rational lane. -/
@[simp] theorem eval_ofPilotQ_normalize (s : Series) :
    HExprQ.eval M (ofSeriesQ (normalize s)) = HExprQ.eval M (ofSeriesQ s) := by
  exact eval_ofSeriesQ_normalize (M := M) s

end PublicAPIQ

end
end BridgePilot
end Hyperseries
end HeytingLean
