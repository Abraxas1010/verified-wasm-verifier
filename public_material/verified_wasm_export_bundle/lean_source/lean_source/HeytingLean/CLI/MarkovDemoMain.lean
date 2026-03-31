import HeytingLean.Topology.Knot.Braid

/-!
# Markov move demo CLI (Kauffman Phase 4, toy)

This executable sanity-checks the braid-layer extensions needed for the “quantum layer” plan:

* inverse crossings are supported (`σᵢ⁻¹` as a negative PD crossing + swapped TL coefficients),
* the TL evaluation agrees with bracket evaluation for small signed braid words,
* and the Jones-style normalised bracket is invariant (on small samples) under the two Markov moves:
  conjugation and ±stabilisation.
-/

namespace HeytingLean.CLI.MarkovDemoMain

open HeytingLean.Topology.Knot
open HeytingLean.Topology.Knot.Reidemeister
open HeytingLean.Topology.Knot.Kauffman
open HeytingLean.Topology.Knot.Braid

private def die (msg : String) : IO UInt32 := do
  IO.eprintln msg
  pure 1

private def ok (b : Bool) (msg : String) : IO Unit := do
  if !b then
    throw (IO.userError msg)

private def okEq {α} [DecidableEq α] (x y : α) (msg : String) : IO Unit :=
  ok (decide (x = y)) msg

private def liftE {α} (ctx : String) : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{ctx}: {e}")

private def sigma (i : Nat) : Gen := { i := i, sign := .pos }
private def sigmaInv (i : Nat) : Gen := { i := i, sign := .neg }

private def jonesOfBraid (n : Nat) (w : List Gen) : Except String LaurentPoly := do
  let s ← Braid.closureSignedPDGraph n w
  Kauffman.SignedPDGraph.normalizedBracket s

private def stabilize (n : Nat) (w : List Gen) (sgn : CurlKind) : List Gen :=
  w ++ [{ i := n - 1, sign := sgn }]

private def checkTLvsBracket (n : Nat) (w : List Gen) (name : String) : IO Unit := do
  let pTL ← liftE s!"{name} evalTL" (Braid.evalTL n w)
  let pPD ← liftE s!"{name} bracketPD" (Braid.bracketPD n w)
  okEq pTL pPD s!"{name}: TL vs bracket mismatch"

private def checkMarkovConjugation (n : Nat) (a b : List Gen) (name : String) : IO Unit := do
  let lhs := a ++ b ++ Braid.Word.inv a
  let p1 ← liftE s!"{name} jones(aba⁻¹)" (jonesOfBraid n lhs)
  let p2 ← liftE s!"{name} jones(b)" (jonesOfBraid n b)
  okEq p1 p2 s!"{name}: conjugation invariance failed"

private def checkMarkovStabilize (n : Nat) (w : List Gen) (sgn : CurlKind) (name : String) : IO Unit := do
  let p1 ← liftE s!"{name} jones(n={n})" (jonesOfBraid n w)
  let w' := stabilize n w sgn
  let p2 ← liftE s!"{name} jones(stabilised)" (jonesOfBraid (n + 1) w')
  okEq p1 p2 s!"{name}: stabilisation invariance failed"

def main (_argv : List String) : IO UInt32 := do
  try
    -- Basic TL-vs-bracket cross-checks, now including inverses.
    checkTLvsBracket 1 [] "B1[]"
    checkTLvsBracket 2 [] "B2[]"
    checkTLvsBracket 2 [sigma 0] "B2[σ0]"
    checkTLvsBracket 2 [sigmaInv 0] "B2[σ0⁻¹]"
    checkTLvsBracket 2 [sigma 0, sigmaInv 0] "B2[σ0 σ0⁻¹]"
    checkTLvsBracket 2 [sigmaInv 0, sigma 0] "B2[σ0⁻¹ σ0]"

    -- Braid relations (and inverse braid relations) on n=3.
    checkTLvsBracket 3 [sigma 0, sigma 1, sigma 0] "B3[σ0σ1σ0]"
    checkTLvsBracket 3 [sigma 1, sigma 0, sigma 1] "B3[σ1σ0σ1]"
    let pL ← liftE "braid rel TL left" (Braid.evalTL 3 [sigma 0, sigma 1, sigma 0])
    let pR ← liftE "braid rel TL right" (Braid.evalTL 3 [sigma 1, sigma 0, sigma 1])
    okEq pL pR "TL braid relation failed (n=3, σ0σ1σ0 = σ1σ0σ1)"

    checkTLvsBracket 3 [sigmaInv 0, sigmaInv 1, sigmaInv 0] "B3[σ0⁻¹σ1⁻¹σ0⁻¹]"
    checkTLvsBracket 3 [sigmaInv 1, sigmaInv 0, sigmaInv 1] "B3[σ1⁻¹σ0⁻¹σ1⁻¹]"
    let pLi ← liftE "inv braid rel TL left" (Braid.evalTL 3 [sigmaInv 0, sigmaInv 1, sigmaInv 0])
    let pRi ← liftE "inv braid rel TL right" (Braid.evalTL 3 [sigmaInv 1, sigmaInv 0, sigmaInv 1])
    okEq pLi pRi "TL inverse braid relation failed (n=3)"

    -- Markov move I: conjugation.
    checkMarkovConjugation 3 [sigma 0] [sigma 1, sigmaInv 0, sigma 1] "Markov conjugation (n=3)"

    -- Markov move II: stabilisation (+ and -).
    checkMarkovStabilize 1 [] .pos "Markov +stabilise (unknot)"
    checkMarkovStabilize 1 [] .neg "Markov -stabilise (unknot)"

    let trefoil : List Gen := [sigma 0, sigma 0, sigma 0]
    checkMarkovStabilize 2 trefoil .pos "Markov +stabilise (trefoil)"
    checkMarkovStabilize 2 trefoil .neg "Markov -stabilise (trefoil)"

    IO.println "markov_demo: ok"
    pure 0
  catch e =>
    die s!"markov_demo: FAILED: {e}"

end HeytingLean.CLI.MarkovDemoMain

open HeytingLean.CLI.MarkovDemoMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.MarkovDemoMain.main args

