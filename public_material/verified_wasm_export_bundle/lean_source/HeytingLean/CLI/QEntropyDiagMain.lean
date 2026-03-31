import HeytingLean.Quantum.QFreeEnergy

/-
CLI helper that numerically checks the spectral logarithm story from
`HeytingLean.Quantum.QFreeEnergy` on tiny diagonal density matrices.
Everything stays in `Float`, so we can exercise it at runtime even
though the Lean definitions live in `ℂ`.
-/

namespace HeytingLean
namespace CLI

noncomputable section

open HeytingLean Quantum
open scoped BigOperators

private def diagWitnessVec : Fin 2 → ℝ := fun _ => (1 / 2 : ℝ)

private lemma diagWitness_nonneg : ∀ i, 0 ≤ diagWitnessVec i := by
  intro i; simp [diagWitnessVec]

private lemma diagWitness_sum : ∑ i, diagWitnessVec i = 1 := by
  classical
  have hsum :
      ∑ i, diagWitnessVec i =
        diagWitnessVec 0 + diagWitnessVec 1 :=
    Fin.sum_univ_two _
  have hEval : diagWitnessVec 0 + diagWitnessVec 1 = 1 := by
    norm_num [diagWitnessVec]
  exact hsum.trans hEval

private def diagWitnessEvidence :
    matrixLogDensity (Density.diagDensity diagWitnessVec diagWitness_nonneg diagWitness_sum) =
      Matrix.diagonal fun i => (Real.log (diagWitnessVec i) : ℂ) :=
  matrixLogDensity_diagDensity diagWitness_nonneg diagWitness_sum

structure Mat2 where
  a11 : Float
  a12 : Float
  a21 : Float
  a22 : Float
  deriving Repr

namespace Mat2

@[simp] def mul (A B : Mat2) : Mat2 :=
  { a11 := A.a11 * B.a11 + A.a12 * B.a21
  , a12 := A.a11 * B.a12 + A.a12 * B.a22
  , a21 := A.a21 * B.a11 + A.a22 * B.a21
  , a22 := A.a21 * B.a12 + A.a22 * B.a22 }

@[simp] def transpose (A : Mat2) : Mat2 :=
  { a11 := A.a11, a12 := A.a21, a21 := A.a12, a22 := A.a22 }

@[simp] def diag (x y : Float) : Mat2 :=
  { a11 := x, a12 := 0.0, a21 := 0.0, a22 := y }

@[simp] def fromColumns (c₁ c₂ : Float × Float) : Mat2 :=
  { a11 := c₁.1, a12 := c₂.1, a21 := c₁.2, a22 := c₂.2 }

private def max2 (x y : Float) : Float := if x < y then y else x

@[simp] def maxAbsDiff (A B : Mat2) : Float :=
  let d11 := Float.abs (A.a11 - B.a11)
  let d12 := Float.abs (A.a12 - B.a12)
  let d21 := Float.abs (A.a21 - B.a21)
  let d22 := Float.abs (A.a22 - B.a22)
  max2 d11 (max2 d12 (max2 d21 d22))

@[simp] def toJson (A : Mat2) : String :=
  let field (k : String) (v : Float) := "\"" ++ k ++ "\":" ++ toString v
  let parts :=
    [ field "a11" A.a11
    , field "a12" A.a12
    , field "a21" A.a21
    , field "a22" A.a22 ]
  "{" ++ String.intercalate "," parts ++ "}"

end Mat2

private def π : Float := 3.141592653589793

private def degToRad (deg : Float) : Float :=
  deg * (π / 180.0)

private def rotation (θ : Float) : Mat2 :=
  let c := Float.cos θ
  let s := Float.sin θ
  { a11 := c, a12 := -s, a21 := s, a22 := c }

private def parseFlag : List String → String → Option String
  | [], _ => none
  | x :: xs, flag =>
      if x = flag then
        match xs with
        | y :: _ => some y
        | [] => none
      else
        parseFlag xs flag

private def parseNatString (s : String) : Option Nat :=
  match String.toNat? s with
  | some n => some n
  | none => none

private def parsePositiveFloat (s : String) : Option Float :=
  match parseNatString s with
  | some n => some (Float.ofNat n)
  | none =>
      match s.splitOn "." with
      | [intPart, fracPart] =>
          let intOpt :=
            if intPart = "" then some 0 else parseNatString intPart
          let fracOpt :=
            if fracPart = "" then some 0 else parseNatString fracPart
          match intOpt, fracOpt with
          | some i, some f =>
              let scale := (10.0 : Float) ^ (Float.ofNat fracPart.length)
              some (Float.ofNat i + Float.ofNat f / scale)
          | _, _ => none
      | _ => none

private def parseFloatLit (sRaw : String) : Option Float :=
  let s := sRaw.trim
  if s = "" then
    none
  else if s.startsWith "-" then
    match parsePositiveFloat (s.drop 1) with
    | some v => some (-v)
    | none => none
  else if s.startsWith "+" then
    parsePositiveFloat (s.drop 1)
  else
    parsePositiveFloat s

private def parseDiag (s : String) : Option (Float × Float) :=
  match s.splitOn "," with
  | [aStr, bStr] =>
      match parseFloatLit aStr, parseFloatLit bStr with
      | some a, some b => some (a, b)
      | _, _ => none
  | _ => none

private def normalizeVec (x y : Float) : (Float × Float) :=
  let n := Float.sqrt (x * x + y * y)
  if Float.abs n < 1e-9 then (1.0, 0.0) else (x / n, y / n)

private def eigenBasis (A : Mat2) : (Float × Float) × (Float × Float) :=
  let trace := A.a11 + A.a22
  let diff := (A.a11 - A.a22) / 2.0
  let delta := Float.sqrt (diff * diff + A.a12 * A.a12)
  let lam1 := trace / 2.0 + delta
  let tol := 1e-9
  let base :=
    if Float.abs A.a12 > tol then
      normalizeVec A.a12 (lam1 - A.a11)
    else if A.a11 ≥ A.a22 then
      (1.0, 0.0)
    else
      (0.0, 1.0)
  let ortho := (-base.2, base.1)
  (base, ortho)

private def spectralLogFromEigen (A : Mat2) :
    Option (Mat2 × Float × Float × Mat2) := do
  let trace := A.a11 + A.a22
  let diff := (A.a11 - A.a22) / 2.0
  let delta := Float.sqrt (diff * diff + A.a12 * A.a12)
  let lam1 := trace / 2.0 + delta
  let lam2 := trace / 2.0 - delta
  if lam1 ≤ 0.0 ∨ lam2 ≤ 0.0 then
    none
  else
    let (v₁, v₂) := eigenBasis A
    let U := Mat2.fromColumns v₁ v₂
    let diagLog := Mat2.diag (Float.log lam1) (Float.log lam2)
    let spectral := Mat2.mul (Mat2.mul U diagLog) (Mat2.transpose U)
    some (spectral, lam1, lam2, U)

private def floatArray (xs : List Float) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"

private def diagLemmaSummary : String :=
  let diag := [0.5, 0.5]
  let logDiag := diag.map Float.log
  "{" ++
    "\"lemma\":\"matrixLogDensity_diagDensity\"," ++
    s!"\"diag\":{floatArray diag}," ++
    s!"\"logDiag\":{floatArray logDiag}" ++
  "}"

def qEntropyDiagMain (argv : List String) : IO Unit := do
  let defaultDiag : Float × Float := (0.7, 0.3)
  let diagStr? := parseFlag argv "--diag"
  let angleStr? := parseFlag argv "--angleDeg"
  let diagVals ←
    match diagStr? with
    | some s =>
        match parseDiag s with
        | some d => pure d
        | none =>
            IO.eprintln s!"invalid --diag '{s}' (expected a,b decimals)"
            IO.Process.exit 1
    | none => pure defaultDiag
  let angleDeg ←
    match angleStr? with
    | some raw =>
        match parseFloatLit raw with
        | some a => pure a
        | none =>
            IO.eprintln s!"invalid --angleDeg '{raw}' (expected decimal degrees)"
            IO.Process.exit 1
    | none => pure 15.0
  let (p₁, p₂) := diagVals
  let tol := 1e-6
  if p₁ ≤ 0.0 ∨ p₂ ≤ 0.0 then
    IO.eprintln "diagonal entries must be positive to take logs"
    IO.Process.exit 1
  if Float.abs ((p₁ + p₂) - 1.0) > tol then
    IO.eprintln s!"probabilities must sum to 1 (got {p₁ + p₂})"
    IO.Process.exit 1
  let θ := degToRad angleDeg
  let R := rotation θ
  let D := Mat2.diag p₁ p₂
  let density := Mat2.mul (Mat2.mul R D) (Mat2.transpose R)
  let entryLog := Mat2.diag (Float.log p₁) (Float.log p₂)
  let targetSpectral := Mat2.mul (Mat2.mul R entryLog) (Mat2.transpose R)
  match spectralLogFromEigen density with
  | none =>
      IO.eprintln "eigenvalue computation failed (nonpositive eigenvalues?)"
      IO.Process.exit 1
  | some (spectral, lam1, lam2, U) =>
      let diff := Mat2.maxAbsDiff spectral targetSpectral
      let out :=
        "{" ++
        s!"\"diag\":{floatArray [p₁, p₂]}," ++
        s!"\"angleDeg\":{toString angleDeg}," ++
        s!"\"density\":{density.toJson}," ++
        s!"\"eigenvalues\":{floatArray [lam1, lam2]}," ++
        s!"\"entryLogDiag\":{floatArray [Float.log p₁, Float.log p₂]}," ++
        s!"\"spectralFromEigen\":{spectral.toJson}," ++
        s!"\"spectralFromRotation\":{targetSpectral.toJson}," ++
        s!"\"formalDiagWitness\":{diagLemmaSummary}," ++
        s!"\"basis\":{U.toJson}," ++
        s!"\"maxAbsDiff\":{toString diff}" ++
        "}"
      IO.println out

end

end CLI
end HeytingLean

def main (argv : List String) : IO Unit :=
  HeytingLean.CLI.qEntropyDiagMain argv
