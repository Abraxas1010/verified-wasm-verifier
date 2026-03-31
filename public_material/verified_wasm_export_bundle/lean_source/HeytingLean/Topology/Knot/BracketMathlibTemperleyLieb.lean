import HeytingLean.Topology.Knot.BracketMathlib
import HeytingLean.Topology.Knot.TemperleyLieb

/-!
# Knot theory: Temperley–Lieb (3-strand) helper facts for the Mathlib-valued bracket

This file packages a small amount of *combinatorial* Temperley–Lieb diagram data used in the
Phase‑1 Reidemeister‑III proof for `Kauffman.bracketGraphML`.

We work with the repository’s executable `TemperleyLieb.Diagram` type (matchings + loop count),
but all polynomial coefficients live in `PolyML := ℤ[T;T⁻¹]` from `BracketMathlib`.

Notes:
- The polynomial layer is noncomputable, but the **diagram compositions** are computable; we use
  `native_decide` to confirm the relevant 3-strand composition identities.
-/

namespace HeytingLean
namespace Topology
namespace Knot

namespace Kauffman

open scoped LaurentPolynomial

open TemperleyLieb

noncomputable section

-- `Std` does not provide `DecidableEq` for `Except` by default; we only need it here to
-- `native_decide` small diagram-composition equalities.
instance instDecidableEqExcept {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α)
  | .ok a, .ok b =>
      match decEq a b with
      | isTrue h => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro hEq; cases hEq; exact h rfl)
  | .error e, .error e' =>
      match decEq e e' with
      | isTrue h => isTrue (by cases h; rfl)
      | isFalse h => isFalse (by intro hEq; cases hEq; exact h rfl)
  | .ok _, .error _ => isFalse (by intro hEq; cases hEq)
  | .error _, .ok _ => isFalse (by intro hEq; cases hEq)

abbrev TL3Diagram : Type :=
  TemperleyLieb.Diagram 3

namespace TL3

def id : TL3Diagram :=
  TemperleyLieb.Diagram.id 3

def e1 : TL3Diagram :=
  { loops := 0, nbr := #[1, 0, 5, 4, 3, 2] }

def e2 : TL3Diagram :=
  { loops := 0, nbr := #[3, 2, 1, 0, 5, 4] }

def e1e2 : TL3Diagram :=
  { loops := 0, nbr := #[1, 0, 3, 2, 5, 4] }

def e2e1 : TL3Diagram :=
  { loops := 0, nbr := #[5, 2, 1, 4, 3, 0] }

theorem compose_id_e1 : TemperleyLieb.Diagram.compose id e1 = .ok e1 := by
  native_decide

theorem compose_id_e2 : TemperleyLieb.Diagram.compose id e2 = .ok e2 := by
  native_decide

theorem compose_e1_id : TemperleyLieb.Diagram.compose e1 id = .ok e1 := by
  native_decide

theorem compose_e2_id : TemperleyLieb.Diagram.compose e2 id = .ok e2 := by
  native_decide

theorem compose_e1_e1 :
    TemperleyLieb.Diagram.compose e1 e1 = .ok { e1 with loops := 1 } := by
  native_decide

theorem compose_e2_e2 :
    TemperleyLieb.Diagram.compose e2 e2 = .ok { e2 with loops := 1 } := by
  native_decide

theorem compose_e1_e2 :
    TemperleyLieb.Diagram.compose e1 e2 = .ok e1e2 := by
  native_decide

theorem compose_e2_e1 :
    TemperleyLieb.Diagram.compose e2 e1 = .ok e2e1 := by
  native_decide

theorem compose_e1e2_e1 :
    TemperleyLieb.Diagram.compose e1e2 e1 = .ok e1 := by
  native_decide

theorem compose_e2e1_e2 :
    TemperleyLieb.Diagram.compose e2e1 e2 = .ok e2 := by
  native_decide

end TL3

/-- A small polynomial identity used in the TL-based braid (R3) simplification. -/
theorem A_mul_d_add_A_pow3 :
    AML * dML + (AML ^ 3 : PolyML) = -(AinvML) := by
  -- `d = -A^2 - A^{-2}` so `A*d + A^3 = -(A^{-1})`.
  have hTpow : (LaurentPolynomial.T (R := ℤ) (1 : ℤ) ^ 3 : PolyML) = LaurentPolynomial.T 3 := by
    -- `T m ^ n = T (n * m)`
    simp
  have hTmul12 : (LaurentPolynomial.T (R := ℤ) (1 : ℤ) * LaurentPolynomial.T (2 : ℤ) : PolyML) =
      LaurentPolynomial.T 3 := by
    -- Use `T_add` in the reverse direction and reduce `1+2`.
    have h := (LaurentPolynomial.T_add (R := ℤ) (m := (1 : ℤ)) (n := (2 : ℤ))).symm
    have h' : (1 : ℤ) + 2 = 3 := by norm_num
    -- Disable `T_mul` to avoid simp loops on commutativity.
    simpa [h', -LaurentPolynomial.T_mul] using h
  have hTmul1m2 :
      (LaurentPolynomial.T (R := ℤ) (1 : ℤ) * LaurentPolynomial.T (-2 : ℤ) : PolyML) =
        LaurentPolynomial.T (-1 : ℤ) := by
    have h := (LaurentPolynomial.T_add (R := ℤ) (m := (1 : ℤ)) (n := (-2 : ℤ))).symm
    have h' : (1 : ℤ) + (-2) = (-1) := by norm_num
    simpa [h', -LaurentPolynomial.T_mul] using h
  -- Now expand and simplify.
  -- Disable `T_mul` to keep simp from permuting monomials.
  simp [AML, AinvML, dML, hTpow, hTmul12, hTmul1m2, mul_add, sub_eq_add_neg, add_left_comm,
    add_comm, -LaurentPolynomial.T_mul]

private theorem A_add_Ainv_mul_d_add_Ainv_pow3 :
    AML + AinvML * dML + (AinvML ^ 3 : PolyML) = 0 := by
  -- Directly expand `d = -A^2 - A^{-2}` and reduce Laurent-monomial arithmetic.
  -- Here `A = T(1)` and `A^{-1} = T(-1)`, so:
  --   A^{-1} * d = -(T 1) - (T (-3)) and A^{-1}^3 = T (-3),
  -- hence `A + A^{-1}*d + A^{-3} = 0`.
  have hAinv_mul_T2 : (AinvML * (LaurentPolynomial.T (R := ℤ) 2) : PolyML) = LaurentPolynomial.T 1 := by
    -- `T(-1) * T(2) = T(1)`.
    have h' : (-1 : ℤ) + 2 = 1 := by norm_num
    have h := (LaurentPolynomial.T_add (R := ℤ) (m := (-1 : ℤ)) (n := (2 : ℤ))).symm
    -- Avoid simp loops from `T_mul`.
    simpa [AinvML, h', -LaurentPolynomial.T_mul] using h
  have hAinv_mul_Tm2 : (AinvML * (LaurentPolynomial.T (R := ℤ) (-2)) : PolyML) = LaurentPolynomial.T (-3) := by
    -- `T(-1) * T(-2) = T(-3)`.
    have h' : (-1 : ℤ) + (-2) = (-3) := by norm_num
    have h := (LaurentPolynomial.T_add (R := ℤ) (m := (-1 : ℤ)) (n := (-2 : ℤ))).symm
    simpa [AinvML, h', -LaurentPolynomial.T_mul] using h
  have hAinv_pow3 : (AinvML ^ 3 : PolyML) = LaurentPolynomial.T (-3) := by
    -- `T(-1)^3 = T(3 * (-1)) = T(-3)`.
    simp [AinvML]
  have hAinv_d : (AinvML * dML : PolyML) = -(LaurentPolynomial.T 1) - LaurentPolynomial.T (-3) := by
    calc
      (AinvML * dML : PolyML)
          = AinvML * (-(LaurentPolynomial.T (R := ℤ) 2) - LaurentPolynomial.T (R := ℤ) (-2)) := by
              rfl
      _ = AinvML * (-(LaurentPolynomial.T (R := ℤ) 2) + -(LaurentPolynomial.T (R := ℤ) (-2))) := by
          simp [sub_eq_add_neg]
      _ = AinvML * (-(LaurentPolynomial.T (R := ℤ) 2)) + AinvML * (-(LaurentPolynomial.T (R := ℤ) (-2))) := by
          simp [mul_add]
      _ = -(AinvML * LaurentPolynomial.T (R := ℤ) 2) + -(AinvML * LaurentPolynomial.T (R := ℤ) (-2)) := by
          simp [mul_neg]
      _ = -(LaurentPolynomial.T (R := ℤ) 1) + -(LaurentPolynomial.T (R := ℤ) (-3)) := by
          simp [hAinv_mul_T2, hAinv_mul_Tm2]
      _ = -(LaurentPolynomial.T (R := ℤ) 1) - LaurentPolynomial.T (R := ℤ) (-3) := by
          simp [sub_eq_add_neg]
  -- Finish by cancellation (commutative additive group).
  calc
    AML + AinvML * dML + (AinvML ^ 3 : PolyML)
        =
          (LaurentPolynomial.T (R := ℤ) (1 : ℤ) : PolyML) +
            (-(LaurentPolynomial.T (R := ℤ) 1) - LaurentPolynomial.T (R := ℤ) (-3)) +
            LaurentPolynomial.T (R := ℤ) (-3) := by
          simp [AML, hAinv_d, hAinv_pow3]
    _ = 0 := by
      simp [sub_eq_add_neg]

/-- The Laurent-monomial identity `A · A⁻¹ = 1` for `PolyML`. -/
private theorem AML_mul_AinvML : (AML * AinvML : PolyML) = 1 := by
  have h := (LaurentPolynomial.T_add (R := ℤ) (m := (1 : ℤ)) (n := (-1 : ℤ))).symm
  have h' : (1 : ℤ) + (-1) = 0 := by norm_num
  -- Disable `T_mul` to avoid simp loops.
  simpa [AML, AinvML, h', -LaurentPolynomial.T_mul] using h

/-- The Laurent-monomial identity `A⁻¹ · A = 1` for `PolyML`. -/
private theorem AinvML_mul_AML : (AinvML * AML : PolyML) = 1 := by
  calc
    AinvML * AML = AML * AinvML := by simp [mul_comm]
    _ = 1 := AML_mul_AinvML

/-- A small hand-rolled linear combination of the five TL₃ basis diagrams we use in Phase 1. -/
structure TL3Expr where
  c_id : PolyML := 0
  c_e1 : PolyML := 0
  c_e2 : PolyML := 0
  c_e1e2 : PolyML := 0
  c_e2e1 : PolyML := 0

namespace TL3Expr

@[ext] theorem ext (a b : TL3Expr)
    (h_id : a.c_id = b.c_id)
    (h_e1 : a.c_e1 = b.c_e1)
    (h_e2 : a.c_e2 = b.c_e2)
    (h_e1e2 : a.c_e1e2 = b.c_e1e2)
    (h_e2e1 : a.c_e2e1 = b.c_e2e1) : a = b := by
  cases a
  cases b
  simp at h_id h_e1 h_e2 h_e1e2 h_e2e1
  cases h_id
  cases h_e1
  cases h_e2
  cases h_e1e2
  cases h_e2e1
  rfl

def zero : TL3Expr := {}

instance : Zero TL3Expr := ⟨zero⟩

def add (a b : TL3Expr) : TL3Expr :=
  { c_id := a.c_id + b.c_id
    c_e1 := a.c_e1 + b.c_e1
    c_e2 := a.c_e2 + b.c_e2
    c_e1e2 := a.c_e1e2 + b.c_e1e2
    c_e2e1 := a.c_e2e1 + b.c_e2e1 }

instance : Add TL3Expr := ⟨add⟩

theorem add_def (a b : TL3Expr) : a + b = TL3Expr.add a b := rfl

def smul (r : PolyML) (a : TL3Expr) : TL3Expr :=
  { c_id := r * a.c_id
    c_e1 := r * a.c_e1
    c_e2 := r * a.c_e2
    c_e1e2 := r * a.c_e1e2
    c_e2e1 := r * a.c_e2e1 }

instance : SMul PolyML TL3Expr := ⟨smul⟩

theorem smul_def (r : PolyML) (a : TL3Expr) : r • a = TL3Expr.smul r a := rfl

@[simp] theorem one_smul (a : TL3Expr) : (1 : PolyML) • a = a := by
  cases a
  apply TL3Expr.ext <;> simp [smul_def, TL3Expr.smul]

def id : TL3Expr := { c_id := 1 }
def e1 : TL3Expr := { c_e1 := 1 }
def e2 : TL3Expr := { c_e2 := 1 }
def e1e2 : TL3Expr := { c_e1e2 := 1 }
def e2e1 : TL3Expr := { c_e2e1 := 1 }

@[simp] theorem id_c_id : (id : TL3Expr).c_id = 1 := by rfl
@[simp] theorem id_c_e1 : (id : TL3Expr).c_e1 = 0 := by rfl
@[simp] theorem id_c_e2 : (id : TL3Expr).c_e2 = 0 := by rfl
@[simp] theorem id_c_e1e2 : (id : TL3Expr).c_e1e2 = 0 := by rfl
@[simp] theorem id_c_e2e1 : (id : TL3Expr).c_e2e1 = 0 := by rfl

@[simp] theorem e1_c_id : (e1 : TL3Expr).c_id = 0 := by rfl
@[simp] theorem e1_c_e1 : (e1 : TL3Expr).c_e1 = 1 := by rfl
@[simp] theorem e1_c_e2 : (e1 : TL3Expr).c_e2 = 0 := by rfl
@[simp] theorem e1_c_e1e2 : (e1 : TL3Expr).c_e1e2 = 0 := by rfl
@[simp] theorem e1_c_e2e1 : (e1 : TL3Expr).c_e2e1 = 0 := by rfl

@[simp] theorem e2_c_id : (e2 : TL3Expr).c_id = 0 := by rfl
@[simp] theorem e2_c_e1 : (e2 : TL3Expr).c_e1 = 0 := by rfl
@[simp] theorem e2_c_e2 : (e2 : TL3Expr).c_e2 = 1 := by rfl
@[simp] theorem e2_c_e1e2 : (e2 : TL3Expr).c_e1e2 = 0 := by rfl
@[simp] theorem e2_c_e2e1 : (e2 : TL3Expr).c_e2e1 = 0 := by rfl

@[simp] theorem e1e2_c_id : (e1e2 : TL3Expr).c_id = 0 := by rfl
@[simp] theorem e1e2_c_e1 : (e1e2 : TL3Expr).c_e1 = 0 := by rfl
@[simp] theorem e1e2_c_e2 : (e1e2 : TL3Expr).c_e2 = 0 := by rfl
@[simp] theorem e1e2_c_e1e2 : (e1e2 : TL3Expr).c_e1e2 = 1 := by rfl
@[simp] theorem e1e2_c_e2e1 : (e1e2 : TL3Expr).c_e2e1 = 0 := by rfl

@[simp] theorem e2e1_c_id : (e2e1 : TL3Expr).c_id = 0 := by rfl
@[simp] theorem e2e1_c_e1 : (e2e1 : TL3Expr).c_e1 = 0 := by rfl
@[simp] theorem e2e1_c_e2 : (e2e1 : TL3Expr).c_e2 = 0 := by rfl
@[simp] theorem e2e1_c_e1e2 : (e2e1 : TL3Expr).c_e1e2 = 0 := by rfl
@[simp] theorem e2e1_c_e2e1 : (e2e1 : TL3Expr).c_e2e1 = 1 := by rfl

@[simp] theorem add_c_id (a b : TL3Expr) : (a + b).c_id = a.c_id + b.c_id := rfl
@[simp] theorem add_c_e1 (a b : TL3Expr) : (a + b).c_e1 = a.c_e1 + b.c_e1 := rfl
@[simp] theorem add_c_e2 (a b : TL3Expr) : (a + b).c_e2 = a.c_e2 + b.c_e2 := rfl
@[simp] theorem add_c_e1e2 (a b : TL3Expr) : (a + b).c_e1e2 = a.c_e1e2 + b.c_e1e2 := rfl
@[simp] theorem add_c_e2e1 (a b : TL3Expr) : (a + b).c_e2e1 = a.c_e2e1 + b.c_e2e1 := rfl

@[simp] theorem smul_c_id (r : PolyML) (a : TL3Expr) : (r • a).c_id = r * a.c_id := rfl
@[simp] theorem smul_c_e1 (r : PolyML) (a : TL3Expr) : (r • a).c_e1 = r * a.c_e1 := rfl
@[simp] theorem smul_c_e2 (r : PolyML) (a : TL3Expr) : (r • a).c_e2 = r * a.c_e2 := rfl
@[simp] theorem smul_c_e1e2 (r : PolyML) (a : TL3Expr) : (r • a).c_e1e2 = r * a.c_e1e2 := rfl
@[simp] theorem smul_c_e2e1 (r : PolyML) (a : TL3Expr) : (r • a).c_e2e1 = r * a.c_e2e1 := rfl

inductive Basis where
  | id | e1 | e2 | e1e2 | e2e1
deriving DecidableEq

def basisDiag : Basis → TL3Diagram
  | .id => TL3.id
  | .e1 => TL3.e1
  | .e2 => TL3.e2
  | .e1e2 => TL3.e1e2
  | .e2e1 => TL3.e2e1

def ofBasis : Basis → TL3Expr
  | .id => id
  | .e1 => e1
  | .e2 => e2
  | .e1e2 => e1e2
  | .e2e1 => e2e1

@[simp] theorem ofBasis_id : ofBasis .id = id := rfl
@[simp] theorem ofBasis_e1 : ofBasis .e1 = e1 := rfl
@[simp] theorem ofBasis_e2 : ofBasis .e2 = e2 := rfl
@[simp] theorem ofBasis_e1e2 : ofBasis .e1e2 = e1e2 := rfl
@[simp] theorem ofBasis_e2e1 : ofBasis .e2e1 = e2e1 := rfl

def coeff (a : TL3Expr) : Basis → PolyML
  | .id => a.c_id
  | .e1 => a.c_e1
  | .e2 => a.c_e2
  | .e1e2 => a.c_e1e2
  | .e2e1 => a.c_e2e1

private def mkFromNbr (nbr : Array Nat) : TL3Expr :=
  if nbr = TL3.id.nbr then ofBasis .id
  else if nbr = TL3.e1.nbr then ofBasis .e1
  else if nbr = TL3.e2.nbr then ofBasis .e2
  else if nbr = TL3.e1e2.nbr then ofBasis .e1e2
  else if nbr = TL3.e2e1.nbr then ofBasis .e2e1
  else 0

private def mulBasis (a b : Basis) : TL3Expr :=
  match TemperleyLieb.Diagram.compose (basisDiag a) (basisDiag b) with
  | .error _ => 0
  | .ok d =>
      (dML ^ d.loops) • mkFromNbr d.nbr

private def sum5 (f : Basis → TL3Expr) : TL3Expr :=
  f .id + f .e1 + f .e2 + f .e1e2 + f .e2e1

def mul (a b : TL3Expr) : TL3Expr :=
  sum5 (fun i =>
    sum5 (fun j =>
      (a.coeff i * b.coeff j) • mulBasis i j))

instance : Mul TL3Expr := ⟨mul⟩

theorem mul_def (a b : TL3Expr) : a * b = TL3Expr.mul a b := rfl

def sigma1 : TL3Expr := (AML • id) + (AinvML • e1)
def sigma2 : TL3Expr := (AML • id) + (AinvML • e2)

-- A small amount of pre-expanded TL₃ arithmetic for the braid relation.
private def sigma12 : TL3Expr :=
  { c_id := AML * AML
    c_e1 := AML * AinvML
    c_e2 := AML * AinvML
    c_e1e2 := AinvML * AinvML }

private def sigma21 : TL3Expr :=
  { c_id := AML * AML
    c_e1 := AML * AinvML
    c_e2 := AML * AinvML
    c_e2e1 := AinvML * AinvML }

private def braidNF : TL3Expr :=
  { c_id := (AML ^ 3 : PolyML)
    c_e1 := AML
    c_e2 := AML
    c_e1e2 := AinvML
    c_e2e1 := AinvML }

@[simp] private theorem coeff_sigma12_id : sigma12.coeff .id = AML * AML := by
  simp [sigma12, coeff]
@[simp] private theorem coeff_sigma12_e1 : sigma12.coeff .e1 = AML * AinvML := by
  simp [sigma12, coeff]
@[simp] private theorem coeff_sigma12_e2 : sigma12.coeff .e2 = AML * AinvML := by
  simp [sigma12, coeff]
@[simp] private theorem coeff_sigma12_e1e2 : sigma12.coeff .e1e2 = AinvML * AinvML := by
  simp [sigma12, coeff]
@[simp] private theorem coeff_sigma12_e2e1 : sigma12.coeff .e2e1 = 0 := by
  simp [sigma12, coeff]

@[simp] private theorem coeff_sigma21_id : sigma21.coeff .id = AML * AML := by
  simp [sigma21, coeff]
@[simp] private theorem coeff_sigma21_e1 : sigma21.coeff .e1 = AML * AinvML := by
  simp [sigma21, coeff]
@[simp] private theorem coeff_sigma21_e2 : sigma21.coeff .e2 = AML * AinvML := by
  simp [sigma21, coeff]
@[simp] private theorem coeff_sigma21_e1e2 : sigma21.coeff .e1e2 = 0 := by
  simp [sigma21, coeff]
@[simp] private theorem coeff_sigma21_e2e1 : sigma21.coeff .e2e1 = AinvML * AinvML := by
  simp [sigma21, coeff]

@[simp] theorem coeff_id_id : (id : TL3Expr).coeff .id = 1 := rfl
@[simp] theorem coeff_id_e1 : (id : TL3Expr).coeff .e1 = 0 := rfl
@[simp] theorem coeff_id_e2 : (id : TL3Expr).coeff .e2 = 0 := rfl
@[simp] theorem coeff_id_e1e2 : (id : TL3Expr).coeff .e1e2 = 0 := rfl
@[simp] theorem coeff_id_e2e1 : (id : TL3Expr).coeff .e2e1 = 0 := rfl

@[simp] theorem coeff_e1_id : (e1 : TL3Expr).coeff .id = 0 := rfl
@[simp] theorem coeff_e1_e1 : (e1 : TL3Expr).coeff .e1 = 1 := rfl
@[simp] theorem coeff_e1_e2 : (e1 : TL3Expr).coeff .e2 = 0 := rfl
@[simp] theorem coeff_e1_e1e2 : (e1 : TL3Expr).coeff .e1e2 = 0 := rfl
@[simp] theorem coeff_e1_e2e1 : (e1 : TL3Expr).coeff .e2e1 = 0 := rfl

@[simp] theorem coeff_e2_id : (e2 : TL3Expr).coeff .id = 0 := rfl
@[simp] theorem coeff_e2_e1 : (e2 : TL3Expr).coeff .e1 = 0 := rfl
@[simp] theorem coeff_e2_e2 : (e2 : TL3Expr).coeff .e2 = 1 := rfl
@[simp] theorem coeff_e2_e1e2 : (e2 : TL3Expr).coeff .e1e2 = 0 := rfl
@[simp] theorem coeff_e2_e2e1 : (e2 : TL3Expr).coeff .e2e1 = 0 := rfl

@[simp] theorem coeff_e1e2_id : (e1e2 : TL3Expr).coeff .id = 0 := rfl
@[simp] theorem coeff_e1e2_e1 : (e1e2 : TL3Expr).coeff .e1 = 0 := rfl
@[simp] theorem coeff_e1e2_e2 : (e1e2 : TL3Expr).coeff .e2 = 0 := rfl
@[simp] theorem coeff_e1e2_e1e2 : (e1e2 : TL3Expr).coeff .e1e2 = 1 := rfl
@[simp] theorem coeff_e1e2_e2e1 : (e1e2 : TL3Expr).coeff .e2e1 = 0 := rfl

@[simp] theorem coeff_e2e1_id : (e2e1 : TL3Expr).coeff .id = 0 := rfl
@[simp] theorem coeff_e2e1_e1 : (e2e1 : TL3Expr).coeff .e1 = 0 := rfl
@[simp] theorem coeff_e2e1_e2 : (e2e1 : TL3Expr).coeff .e2 = 0 := rfl
@[simp] theorem coeff_e2e1_e1e2 : (e2e1 : TL3Expr).coeff .e1e2 = 0 := rfl
@[simp] theorem coeff_e2e1_e2e1 : (e2e1 : TL3Expr).coeff .e2e1 = 1 := rfl

@[simp] theorem coeff_sigma1_id : sigma1.coeff .id = AML := by simp [sigma1, coeff, TL3Expr.id, TL3Expr.e1]
@[simp] theorem coeff_sigma1_e1 : sigma1.coeff .e1 = AinvML := by simp [sigma1, coeff, TL3Expr.id, TL3Expr.e1]
@[simp] theorem coeff_sigma1_e2 : sigma1.coeff .e2 = 0 := by simp [sigma1, coeff, TL3Expr.id, TL3Expr.e1]
@[simp] theorem coeff_sigma1_e1e2 : sigma1.coeff .e1e2 = 0 := by simp [sigma1, coeff, TL3Expr.id, TL3Expr.e1]
@[simp] theorem coeff_sigma1_e2e1 : sigma1.coeff .e2e1 = 0 := by simp [sigma1, coeff, TL3Expr.id, TL3Expr.e1]

@[simp] theorem coeff_sigma2_id : sigma2.coeff .id = AML := by simp [sigma2, coeff, TL3Expr.id, TL3Expr.e2]
@[simp] theorem coeff_sigma2_e1 : sigma2.coeff .e1 = 0 := by simp [sigma2, coeff, TL3Expr.id, TL3Expr.e2]
@[simp] theorem coeff_sigma2_e2 : sigma2.coeff .e2 = AinvML := by simp [sigma2, coeff, TL3Expr.id, TL3Expr.e2]
@[simp] theorem coeff_sigma2_e1e2 : sigma2.coeff .e1e2 = 0 := by simp [sigma2, coeff, TL3Expr.id, TL3Expr.e2]
@[simp] theorem coeff_sigma2_e2e1 : sigma2.coeff .e2e1 = 0 := by simp [sigma2, coeff, TL3Expr.id, TL3Expr.e2]

@[simp] private theorem mkFromNbr_id : mkFromNbr TL3.id.nbr = ofBasis .id := by
  simp [mkFromNbr]

@[simp] private theorem mkFromNbr_e1 : mkFromNbr TL3.e1.nbr = ofBasis .e1 := by
  have h1 : TL3.e1.nbr ≠ TL3.id.nbr := by decide
  simp [mkFromNbr, h1]

@[simp] private theorem mkFromNbr_e2 : mkFromNbr TL3.e2.nbr = ofBasis .e2 := by
  have h1 : TL3.e2.nbr ≠ TL3.id.nbr := by decide
  have h2 : TL3.e2.nbr ≠ TL3.e1.nbr := by decide
  simp [mkFromNbr, h1, h2]

@[simp] private theorem mkFromNbr_e1e2 : mkFromNbr TL3.e1e2.nbr = ofBasis .e1e2 := by
  have h1 : TL3.e1e2.nbr ≠ TL3.id.nbr := by decide
  have h2 : TL3.e1e2.nbr ≠ TL3.e1.nbr := by decide
  have h3 : TL3.e1e2.nbr ≠ TL3.e2.nbr := by decide
  simp [mkFromNbr, h1, h2, h3]

@[simp] private theorem mkFromNbr_e2e1 : mkFromNbr TL3.e2e1.nbr = ofBasis .e2e1 := by
  have h1 : TL3.e2e1.nbr ≠ TL3.id.nbr := by decide
  have h2 : TL3.e2e1.nbr ≠ TL3.e1.nbr := by decide
  have h3 : TL3.e2e1.nbr ≠ TL3.e2.nbr := by decide
  have h4 : TL3.e2e1.nbr ≠ TL3.e1e2.nbr := by decide
  simp [mkFromNbr, h1, h2, h3, h4]

@[simp] private theorem mulBasis_id_id : mulBasis .id .id = ofBasis .id := by
  -- Computation: `id ∘ id = id` and creates no loops.
  have h : TemperleyLieb.Diagram.compose TL3.id TL3.id = .ok TL3.id := by
    native_decide
  have hloops : TL3.id.loops = 0 := by
    simp [TL3.id, TemperleyLieb.Diagram.id]
  simp [mulBasis, basisDiag, h]
  -- Reduce the remaining `dML ^ loops` factor.
  rw [hloops]
  simp

@[simp] private theorem mulBasis_id_e1 : mulBasis .id .e1 = ofBasis .e1 := by
  simp [mulBasis, basisDiag, TL3.compose_id_e1]
  simp [TL3.e1]

@[simp] private theorem mulBasis_id_e2 : mulBasis .id .e2 = ofBasis .e2 := by
  simp [mulBasis, basisDiag, TL3.compose_id_e2]
  simp [TL3.e2]

@[simp] private theorem mulBasis_e1_id : mulBasis .e1 .id = ofBasis .e1 := by
  simp [mulBasis, basisDiag, TL3.compose_e1_id]
  simp [TL3.e1]

@[simp] private theorem mulBasis_e2_id : mulBasis .e2 .id = ofBasis .e2 := by
  simp [mulBasis, basisDiag, TL3.compose_e2_id]
  simp [TL3.e2]

@[simp] private theorem mulBasis_e1_e1 : mulBasis .e1 .e1 = (dML • ofBasis .e1) := by
  simp [mulBasis, basisDiag, TL3.compose_e1_e1, pow_succ]

@[simp] private theorem mulBasis_e2_e2 : mulBasis .e2 .e2 = (dML • ofBasis .e2) := by
  simp [mulBasis, basisDiag, TL3.compose_e2_e2, pow_succ]

@[simp] private theorem mulBasis_e1_e2 : mulBasis .e1 .e2 = ofBasis .e1e2 := by
  simp [mulBasis, basisDiag, TL3.compose_e1_e2]
  simp [TL3.e1e2]

@[simp] private theorem mulBasis_e2_e1 : mulBasis .e2 .e1 = ofBasis .e2e1 := by
  simp [mulBasis, basisDiag, TL3.compose_e2_e1]
  simp [TL3.e2e1]

@[simp] private theorem mulBasis_e1e2_id : mulBasis .e1e2 .id = ofBasis .e1e2 := by
  have h : TemperleyLieb.Diagram.compose TL3.e1e2 TL3.id = .ok TL3.e1e2 := by
    native_decide
  simp [mulBasis, basisDiag, h]
  simp [TL3.e1e2]

@[simp] private theorem mulBasis_e2e1_id : mulBasis .e2e1 .id = ofBasis .e2e1 := by
  have h : TemperleyLieb.Diagram.compose TL3.e2e1 TL3.id = .ok TL3.e2e1 := by
    native_decide
  simp [mulBasis, basisDiag, h]
  simp [TL3.e2e1]

@[simp] private theorem mulBasis_e1e2_e1 : mulBasis .e1e2 .e1 = ofBasis .e1 := by
  simp [mulBasis, basisDiag, TL3.compose_e1e2_e1]
  simp [TL3.e1]

@[simp] private theorem mulBasis_e2e1_e2 : mulBasis .e2e1 .e2 = ofBasis .e2 := by
  simp [mulBasis, basisDiag, TL3.compose_e2e1_e2]
  simp [TL3.e2]

@[simp] theorem braid_relation : (sigma1 * sigma2) * sigma1 = (sigma2 * sigma1) * sigma2 := by
  have h12 : sigma1 * sigma2 = sigma12 := by
    apply TL3Expr.ext
    · simp [sigma12, mul_def, TL3Expr.mul, sum5]
    · -- Commutes in `PolyML`.
      simp [sigma12, mul_def, TL3Expr.mul, sum5, mul_comm]
    · simp [sigma12, mul_def, TL3Expr.mul, sum5]
    · simp [sigma12, mul_def, TL3Expr.mul, sum5]
    · simp [sigma12, mul_def, TL3Expr.mul, sum5]
  have h21 : sigma2 * sigma1 = sigma21 := by
    apply TL3Expr.ext
    · simp [sigma21, mul_def, TL3Expr.mul, sum5]
    · simp [sigma21, mul_def, TL3Expr.mul, sum5]
    · -- Commutes in `PolyML`.
      simp [sigma21, mul_def, TL3Expr.mul, sum5, mul_comm]
    · simp [sigma21, mul_def, TL3Expr.mul, sum5]
    · simp [sigma21, mul_def, TL3Expr.mul, sum5]

  have hL : sigma12 * sigma1 = braidNF := by
    apply TL3Expr.ext
    · -- `AML^3` vs `AML*AML*AML`.
      simp [braidNF, mul_def, TL3Expr.mul, sum5, pow_succ, mul_assoc]
    · -- This coefficient uses `e₁^2 = d·e₁` and the polynomial identity `A + A⁻¹·d + A⁻³ = 0`.
      have hpoly := A_add_Ainv_mul_d_add_Ainv_pow3
      -- Collapse diagram multiplication; it remains to simplify the coefficient expression using `hpoly`.
      simp [braidNF, mul_def, TL3Expr.mul, sum5]
      -- Simplify Laurent-monomial factors without triggering `simp` loops on `T_mul`.
      simp [mul_assoc, AML_mul_AinvML]
      calc
        AML + (AML + AinvML * dML) + AinvML * (AinvML * AinvML)
            = AML + (AML + AinvML * dML) + (AinvML ^ 3 : PolyML) := by
                simp [pow_succ, mul_assoc]
        _ = AML + (AML + AinvML * dML + (AinvML ^ 3 : PolyML)) := by
              simp [add_assoc]
        _ = AML := by
              simp [hpoly]
    · simp [braidNF, mul_def, TL3Expr.mul, sum5, AML_mul_AinvML, mul_assoc]
    · simp [braidNF, mul_def, TL3Expr.mul, sum5, AinvML_mul_AML, mul_assoc]
    ·
      -- `AML · AinvML^2 = AinvML` (as a Laurent-monomial identity).
      simp [braidNF, mul_def, TL3Expr.mul, sum5]
      have h : AML * AinvML * AinvML = AinvML := by
        calc
          AML * AinvML * AinvML = (AML * AinvML) * AinvML := by rfl
          _ = 1 * AinvML := by
            simp [AML_mul_AinvML]
          _ = AinvML := by
            simp
      simpa [mul_assoc] using h

  have hR : sigma21 * sigma2 = braidNF := by
    apply TL3Expr.ext
    · simp [braidNF, mul_def, TL3Expr.mul, sum5, pow_succ, mul_assoc]
    · simp [braidNF, mul_def, TL3Expr.mul, sum5, AML_mul_AinvML, mul_assoc]
    · -- Symmetric to `hL` with `e₂^2 = d·e₂`.
      have hpoly := A_add_Ainv_mul_d_add_Ainv_pow3
      simp [braidNF, mul_def, TL3Expr.mul, sum5]
      simp [mul_assoc, AML_mul_AinvML]
      calc
        AML + (AML + AinvML * dML) + AinvML * (AinvML * AinvML)
            = AML + (AML + AinvML * dML) + (AinvML ^ 3 : PolyML) := by
                simp [pow_succ, mul_assoc]
        _ = AML + (AML + AinvML * dML + (AinvML ^ 3 : PolyML)) := by
              simp [add_assoc]
        _ = AML := by
              simp [hpoly]
    ·
      -- `AML · AinvML^2 = AinvML`.
      simp [braidNF, mul_def, TL3Expr.mul, sum5]
      have h : AML * AinvML * AinvML = AinvML := by
        calc
          AML * AinvML * AinvML = (AML * AinvML) * AinvML := by rfl
          _ = 1 * AinvML := by
            simp [AML_mul_AinvML]
          _ = AinvML := by
            simp
      simpa [mul_assoc] using h
    ·
      simp [braidNF, mul_def, TL3Expr.mul, sum5]
      -- `AinvML · (AinvML · AML) = AinvML`.
      simp [mul_assoc, AinvML_mul_AML]

  -- Rewrite the intermediate products and compare the normal forms.
  calc
    (sigma1 * sigma2) * sigma1 = sigma12 * sigma1 := by simp [h12]
    _ = braidNF := hL
    _ = sigma21 * sigma2 := by simpa using hR.symm
    _ = (sigma2 * sigma1) * sigma2 := by simp [h21]

end TL3Expr

end

end Kauffman

end Knot
end Topology
end HeytingLean
