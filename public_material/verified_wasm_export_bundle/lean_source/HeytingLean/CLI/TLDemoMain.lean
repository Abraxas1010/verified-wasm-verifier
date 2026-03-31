import HeytingLean.Topology.Knot.Braid

/-!
# Temperley–Lieb demo CLI (Phase 2)

This executable cross-checks the Kauffman bracket of a closed braid (via PD encoding)
against a compositional Temperley–Lieb evaluation, and sanity-checks a few TL relations.
-/

namespace HeytingLean.CLI.TLDemoMain

open HeytingLean.Topology.Knot
open HeytingLean.Topology.Knot.Kauffman
open HeytingLean.Topology.Knot.Braid
open HeytingLean.Topology.Knot.TemperleyLieb

private def die (msg : String) : IO UInt32 := do
  IO.eprintln msg
  pure 1

private def ok (b : Bool) (msg : String) : IO Unit := do
  if !b then
    throw (IO.userError msg)

private def okEq {α} [DecidableEq α] (x y : α) (msg : String) : IO Unit :=
  ok (decide (x = y)) msg

private def checkBraid (n : Nat) (gens : List Gen) (name : String) : IO Unit := do
  let pTL ←
    match Braid.evalTL n gens with
    | .ok p => pure p
    | .error e => throw (IO.userError s!"{name}: evalTL error: {e}")
  let pPD ←
    match Braid.bracketPD n gens with
    | .ok p => pure p
    | .error e => throw (IO.userError s!"{name}: bracketPD error: {e}")
  okEq pTL pPD s!"{name}: TL vs bracket mismatch"

private def checkTLRelations : IO Unit := do
  -- n=3: e0^2 = d*e0 and e0 e1 e0 = e0
  let e0 ←
    match Diagram.gen 3 0 with
    | .ok d => pure d
    | .error e => throw (IO.userError s!"gen e0 error: {e}")
  let e1 ←
    match Diagram.gen 3 1 with
    | .ok d => pure d
    | .error e => throw (IO.userError s!"gen e1 error: {e}")
  let e0E : Diagram.Expr 3 := Diagram.Expr.ofDiagram e0
  let e1E : Diagram.Expr 3 := Diagram.Expr.ofDiagram e1
  let e0sq ←
    match Diagram.Expr.mul e0E e0E with
    | .ok x => pure x
    | .error e => throw (IO.userError s!"e0^2 error: {e}")
  let rhs := Diagram.Expr.ofDiagram e0 Kauffman.d
  okEq e0sq.sortedTerms rhs.sortedTerms "TL relation failed: e0^2 = d*e0 (n=3)"

  let e0e1 ←
    match Diagram.Expr.mul e0E e1E with
    | .ok x => pure x
    | .error e => throw (IO.userError s!"e0*e1 error: {e}")
  let e0e1e0 ←
    match Diagram.Expr.mul e0e1 e0E with
    | .ok x => pure x
    | .error e => throw (IO.userError s!"e0*e1*e0 error: {e}")
  okEq e0e1e0.sortedTerms e0E.sortedTerms "TL relation failed: e0 e1 e0 = e0 (n=3)"

  -- n=4: e0 and e2 commute
  let e0_4 ←
    match Diagram.gen 4 0 with
    | .ok d => pure d
    | .error e => throw (IO.userError s!"gen e0(4) error: {e}")
  let e2_4 ←
    match Diagram.gen 4 2 with
    | .ok d => pure d
    | .error e => throw (IO.userError s!"gen e2(4) error: {e}")
  let e0_4E : Diagram.Expr 4 := Diagram.Expr.ofDiagram e0_4
  let e2_4E : Diagram.Expr 4 := Diagram.Expr.ofDiagram e2_4
  let l ←
    match Diagram.Expr.mul e0_4E e2_4E with
    | .ok x => pure x
    | .error e => throw (IO.userError s!"e0*e2 error: {e}")
  let r ←
    match Diagram.Expr.mul e2_4E e0_4E with
    | .ok x => pure x
    | .error e => throw (IO.userError s!"e2*e0 error: {e}")
  okEq l.sortedTerms r.sortedTerms "TL relation failed: e0 e2 = e2 e0 (n=4)"

def main (_argv : List String) : IO UInt32 := do
  try
    checkTLRelations

    -- Cross-check a few closed braids.
    checkBraid 2 [] "braid(n=2, [])"
    checkBraid 2 [{ i := 0 }] "braid(n=2, [σ0])"
    checkBraid 2 [{ i := 0 }, { i := 0 }] "braid(n=2, [σ0,σ0])"

    -- Braid relation σ0 σ1 σ0 = σ1 σ0 σ1 (n=3), checked via TL-vs-bracket for each word.
    checkBraid 3 [{ i := 0 }, { i := 1 }, { i := 0 }] "braid(n=3, [σ0,σ1,σ0])"
    checkBraid 3 [{ i := 1 }, { i := 0 }, { i := 1 }] "braid(n=3, [σ1,σ0,σ1])"

    let pL ←
      match Braid.evalTL 3 [{ i := 0 }, { i := 1 }, { i := 0 }] with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"TL eval (left) error: {e}")
    let pR ←
      match Braid.evalTL 3 [{ i := 1 }, { i := 0 }, { i := 1 }] with
      | .ok p => pure p
      | .error e => throw (IO.userError s!"TL eval (right) error: {e}")
    okEq pL pR "TL braid relation check failed: σ0σ1σ0 = σ1σ0σ1 (n=3)"

    IO.println "tl_demo: ok"
    pure 0
  catch e =>
    die s!"tl_demo: FAILED: {e}"

end HeytingLean.CLI.TLDemoMain

open HeytingLean.CLI.TLDemoMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.TLDemoMain.main args

