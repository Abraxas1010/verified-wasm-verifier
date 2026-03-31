import HeytingLean.Topology.Knot.ArtinBraidGroup.Word

/-!
# Braid word ↔ presented braid group alignment demo (Phase 6)

This executable checks that the permutation action induced by:
1. interpreting a braid word as an element of the presented Artin braid group `Bₙ` and then
   applying the canonical representation `Bₙ → Sₙ`, and
2. directly folding adjacent transpositions along the braid word,
agree on a small suite of examples.
-/

namespace HeytingLean.CLI.BraidPermAlignmentMain

open HeytingLean.Topology.Knot
open HeytingLean.Topology.Knot.Reidemeister
open HeytingLean.Topology.Knot.Braid
open HeytingLean.Topology.Knot.ArtinBraid

private def die (msg : String) : IO UInt32 := do
  IO.eprintln msg
  pure 1

private def ok (b : Bool) (msg : String) : IO Unit := do
  if !b then
    throw (IO.userError msg)

private def permEq (n : Nat) (p q : Equiv.Perm (Fin n)) : Bool :=
  (List.finRange n).all (fun x => decide (p x = q x))

private def okPermEq (n : Nat) (p q : Equiv.Perm (Fin n)) (msg : String) : IO Unit :=
  ok (permEq n p q) msg

private def liftE {α} (ctx : String) : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{ctx}: {e}")

private def σ (i : Nat) : Gen := { i := i, sign := .pos }
private def σinv (i : Nat) : Gen := { i := i, sign := .neg }

private def check (n : Nat) (w : List Gen) (name : String) : IO Unit := do
  let pWord ← liftE s!"{name} Word.toPerm" (ArtinBraid.Word.toPerm n w)
  let pGrp ←
    liftE s!"{name} Word.toBraidGroup" (ArtinBraid.Word.toBraidGroup n w) >>= fun bg =>
      pure (ArtinBraid.PermRep.toPerm (n := n) bg)
  okPermEq n pGrp pWord s!"{name}: permutation mismatch"

def main (_argv : List String) : IO UInt32 := do
  try
    -- Basic sanity: empty word.
    check 1 [] "B1[]"
    check 2 [] "B2[]"

    -- Braid relation on n=3 (σ0 σ1 σ0 = σ1 σ0 σ1) at the permutation level.
    check 3 [σ 0, σ 1, σ 0] "B3[σ0σ1σ0]"
    check 3 [σ 1, σ 0, σ 1] "B3[σ1σ0σ1]"

    let p1 ← liftE "braid rel left" (ArtinBraid.Word.toPerm 3 [σ 0, σ 1, σ 0])
    let p2 ← liftE "braid rel right" (ArtinBraid.Word.toPerm 3 [σ 1, σ 0, σ 1])
    okPermEq 3 p1 p2 "B3 braid relation mismatch in S3"

    -- Far commutation on n=4 (σ0 σ2 = σ2 σ0) at the permutation level.
    let q1 ← liftE "comm left" (ArtinBraid.Word.toPerm 4 [σ 0, σ 2])
    let q2 ← liftE "comm right" (ArtinBraid.Word.toPerm 4 [σ 2, σ 0])
    okPermEq 4 q1 q2 "B4 far commutation mismatch in S4"

    -- Sign does not matter for the symmetric-group action (transpositions are involutions).
    let rPos ← liftE "sign pos" (ArtinBraid.Word.toPerm 4 [σ 1, σ 2, σ 1])
    let rNeg ← liftE "sign neg" (ArtinBraid.Word.toPerm 4 [σinv 1, σinv 2, σinv 1])
    okPermEq 4 rPos rNeg "sign should not affect S_n action"

    IO.println "braid_perm_alignment_demo: ok"
    pure 0
  catch e =>
    die s!"braid_perm_alignment_demo: FAILED: {e}"

end HeytingLean.CLI.BraidPermAlignmentMain

open HeytingLean.CLI.BraidPermAlignmentMain in
def main (args : List String) : IO UInt32 :=
  HeytingLean.CLI.BraidPermAlignmentMain.main args
