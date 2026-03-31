import HeytingLean.Numbers.Ordinal.Notation
import HeytingLean.Numbers.Surreal.TransfinitePreGame

/-!
# Surreal.Hyperseries

SN-019 baseline pilot: a finite-support hyperseries/transseries interface over
transfinite exponents (`OrdinalCNF`).

This is intentionally restricted:
- finite term lists (no infinite support),
- executable add/mul/truncate/normalize operations,
- structural order signal via maximal exponent.

It provides a concrete launchpad for omnific-index and transseries experiments
without claiming full omnific/transseries semantics.
-/

namespace HeytingLean
namespace Numbers
namespace Surreal
namespace Hyperseries

open HeytingLean.Numbers.Ordinal
open HeytingLean.Numbers.Surreal.TransfinitePreGame

/-- A finite hyperseries term `c * ω^e` in pilot representation. -/
structure Term where
  coeff : Int
  exp : OrdinalCNF
  deriving Repr, DecidableEq

/-- Finite-support pilot series (list representation). -/
abbrev Series := List Term

/-- Zero series. -/
def zero : Series := []

/-- Singleton monomial series. -/
def monomial (c : Int) (e : OrdinalCNF) : Series := [{ coeff := c, exp := e }]

/-- Pilot series addition as concatenation (normalization can be applied separately). -/
def add (x y : Series) : Series := x ++ y

/-- Multiplication of terms: coefficients multiply, exponents add. -/
def mulTerm (a b : Term) : Term :=
  { coeff := a.coeff * b.coeff
    exp := a.exp + b.exp }

/-- Pilot Cauchy product over finite supports. -/
def mul (x y : Series) : Series :=
  x.foldr (fun a acc => y.map (fun b => mulTerm a b) ++ acc) []

/-- Keep only terms with exponent bounded by `θ`. -/
def truncate (θ : OrdinalCNF) (s : Series) : Series :=
  s.filter (fun t => t.exp ≤ θ)

/-- Remove zero-coefficient terms. -/
def normalize (s : Series) : Series :=
  s.filter (fun t => t.coeff ≠ 0)

/-- Order signal: largest exponent present (or `0` for the empty series). -/
def order : Series → OrdinalCNF
  | [] => 0
  | t :: ts => OrdinalCNF.max t.exp (order ts)

/-- Omnific-style index pilot (integer payload + transfinite scale). -/
structure OmnificIndex where
  integerPart : Int
  transfinitePart : OrdinalCNF
  deriving Repr, DecidableEq

/-- Convert an omnific index into a singleton pilot series. -/
def indexSeries (k : OmnificIndex) : Series :=
  monomial k.integerPart k.transfinitePart

/-- Minimal transseries state: principal + correction parts. -/
structure TransseriesState where
  principal : Series
  correction : Series
  deriving Repr, DecidableEq

/-- One executable pilot update step:
add correction into principal, and square+truncate correction by its current order.
-/
def transseriesStep (s : TransseriesState) : TransseriesState :=
  { principal := add s.principal s.correction
    correction := truncate (order s.correction) (mul s.correction s.correction) }

/-- Lift compact transfinite pre-game birthdays into hyperseries monomials. -/
def fromBirth (g : TransfinitePreGame.PreGame) : Series :=
  monomial 1 (TransfinitePreGame.birth g)

@[simp] theorem length_add (x y : Series) :
    (add x y).length = x.length + y.length := by
  simp [add]

@[simp] theorem truncate_idem (θ : OrdinalCNF) (s : Series) :
    truncate θ (truncate θ s) = truncate θ s := by
  simp [truncate]

@[simp] theorem normalize_idem (s : Series) :
    normalize (normalize s) = normalize s := by
  simp [normalize]

@[simp] theorem mul_monomial (c₁ c₂ : Int) (e₁ e₂ : OrdinalCNF) :
    mul (monomial c₁ e₁) (monomial c₂ e₂) = monomial (c₁ * c₂) (e₁ + e₂) := by
  simp [mul, monomial, mulTerm]

@[simp] theorem order_zero : order zero = 0 := rfl

@[simp] theorem order_monomial (c : Int) (e : OrdinalCNF) :
    order (monomial c e) = OrdinalCNF.max e 0 := rfl

@[simp] theorem order_add_nil_left (x : Series) :
    order (add [] x) = order x := by
  simp [add]

@[simp] theorem order_add_nil_right (x : Series) :
    order (add x []) = order x := by
  induction x with
  | nil => simp [add, order]
  | cons t ts ih =>
      simp [add, order]

end Hyperseries
end Surreal
end Numbers
end HeytingLean
