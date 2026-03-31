import HeytingLean.LoF.Combinators.Differential.GradientDescent

open HeytingLean.LoF
open HeytingLean.LoF.Combinators.Differential

open HeytingLean.LoF.Combinators.Differential.Compute

def main (_argv : List String) : IO Unit := do
  IO.println "[differential_sky_demo] compute-backend demo (Rat coefficients)"
  -- A tiny “learning” target: w* · x = 2·(K x) + 1·(S x)
  let params : List Comb := [.K, .S]
  let x : FSum := Compute.single .Y
  let y : FSum := Compute.add (Compute.smul 2 (Compute.single (.app .K .Y))) (Compute.single (.app .S .Y))
  let cfg : Compute.GDConfig :=
    { learningRate := (1 : Rat) / 5
      iterations := 12
      params := params }
  let examples : List Compute.IOExample :=
    [{ input := x, expected := y }]
  let st := Compute.gradientDescentLoop cfg examples []
  IO.println s!"x = {showFSum x}"
  IO.println s!"target y = {showFSum y}"
  IO.println s!"learned w = {showFSum st.currentWeights}"
  IO.println s!"loss(w) = {toString st.currentLoss}"
  -- Also show a one-step reduction superposition.
  let t : Comb := .app (.app .K .S) .Y
  IO.println s!"stepSum({reprStr t}) = {showFSum (stepSum t)}"
