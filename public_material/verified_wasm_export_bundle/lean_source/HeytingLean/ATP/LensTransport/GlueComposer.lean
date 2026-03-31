import HeytingLean.ATP.LensTransport.LensMove
import HeytingLean.ATP.DifferentiableATP.SheafTransport
import HeytingLean.ATP.DifferentiableATP.SheafResolution

/-
- source_type: ATP infrastructure (sheaf glue for search)
- attribution_status: n/a
- claim_status: n/a
- proof_status: proved
-/

namespace HeytingLean
namespace ATP
namespace LensTransport

open HeytingLean.Embeddings
open HeytingLean.LoF.Combinators.Differential.Compute

/-- A partial proof obtained in a specific lens. -/
structure LensLocalProof where
  /-- The lens in which this proof was found. -/
  lens : LensID
  /-- The proof term (an FSum in the lens basis). -/
  proof : FSum
  /-- The subgoal this proof addresses. -/
  subgoal : String
  deriving Repr

/-- A glued proof assembled from local proofs in different lenses. -/
structure GluedProof where
  /-- The target lens for the assembled proof. -/
  targetLens : LensID
  /-- The assembled proof term. -/
  assembledProof : FSum
  /-- Which local proofs were used. -/
  sources : List LensLocalProof
  /-- Whether the cocycle condition was verified. -/
  cocycleVerified : Bool
  deriving Repr

private def coeffAt (rows : FSum) (comb : HeytingLean.LoF.Comb) : Rat :=
  rows.foldl
    (fun acc tc => if tc.1 == comb then acc + tc.2 else acc)
    0

private def overlapBasis (target left right : LensID) : List HeytingLean.LoF.Comb :=
  (DifferentiableATP.basisForLens target).filter (fun c =>
    c ∈ DifferentiableATP.basisForLens left &&
    c ∈ DifferentiableATP.basisForLens right)

private def agreeOnOverlap
    (target : LensID)
    (left right : LensID × FSum) : Bool :=
  let basis := overlapBasis target left.1 right.1
  basis.all (fun c => coeffAt left.2 c == coeffAt right.2 c)

private def pairwiseAgreeOnOverlaps
    (target : LensID)
    (rows : List (LensID × FSum)) : Bool :=
  let rec go : List (LensID × FSum) → Bool
    | [] => true
    | x :: xs => xs.all (fun y => agreeOnOverlap target x y) && go xs
  go rows

private def transportDirect (src dst : LensID) (proof : FSum) : FSum :=
  DifferentiableATP.LaxCrossLensTransport.forward DifferentiableATP.sheafTransport src dst proof

private def pathIndependentToTarget (src target : LensID) (proof : FSum) : Bool :=
  let direct := transportDirect src target proof
  let mids := allLenses.filter (fun mid =>
    basisSubsetB src mid &&
    basisSubsetB mid target)
  mids.all (fun mid =>
    let viaMid := transportDirect mid target (transportDirect src mid proof)
    viaMid == direct)

private def verifyCocycle (target : LensID) (rows : List (LensID × FSum)) : Bool :=
  pairwiseAgreeOnOverlaps target rows &&
  rows.all (fun row => pathIndependentToTarget row.1 target row.2)

private def chooseCoeff
    (rows : List (LensID × FSum))
    (comb : HeytingLean.LoF.Comb) : Rat :=
  match rows.find? (fun row => coeffAt row.2 comb != 0) with
  | some row => coeffAt row.2 comb
  | none => 0

private def mergeProjected (target : LensID) (rows : List (LensID × FSum)) : FSum :=
  (DifferentiableATP.basisForLens target).foldr
    (fun comb acc =>
      let coeff := chooseCoeff rows comb
      if coeff == 0 then acc else (comb, coeff) :: acc)
    []

/-- Attempt to glue local proofs from different lenses into a single proof. -/
def glueLocalProofs
    (targetLens : LensID)
    (locals : List LensLocalProof) :
    Option GluedProof :=
  if !(locals.all (fun lp => isSafeTransport lp.lens targetLens)) then
    none
  else
    let projected := locals.map (fun lp => (lp.lens, DifferentiableATP.lensProjection targetLens lp.proof))
    let cocycleOK := verifyCocycle targetLens projected
    if !cocycleOK then
      none
    else
      let merged := mergeProjected targetLens projected
      some {
        targetLens := targetLens
        assembledProof := merged
        sources := locals
        cocycleVerified := true
      }

/-- Gluing a singleton local proof succeeds under safe transport. -/
theorem glue_singleton (targetLens : LensID) (lp : LensLocalProof)
    (hsafe : isSafeTransport lp.lens targetLens = true)
    (hcocycle : verifyCocycle targetLens
      [(lp.lens, DifferentiableATP.lensProjection targetLens lp.proof)] = true) :
    (glueLocalProofs targetLens [lp]).isSome = true := by
  simp [glueLocalProofs, hsafe, hcocycle]

/-- Gluing two proofs from the same lens succeeds when cocycle checks pass. -/
theorem glue_same_lens (lens : LensID)
    (lp1 lp2 : LensLocalProof)
    (h1 : lp1.lens = lens) (h2 : lp2.lens = lens)
    (hcocycle : verifyCocycle lens
      [ (lp1.lens, DifferentiableATP.lensProjection lens lp1.proof)
      , (lp2.lens, DifferentiableATP.lensProjection lens lp2.proof)
      ] = true) :
    (glueLocalProofs lens [lp1, lp2]).isSome = true := by
  have hs1 : isSafeTransport lp1.lens lens = true := by
    simpa [h1] using isSafeTransport_refl lens
  have hs2 : isSafeTransport lp2.lens lens = true := by
    simpa [h2] using isSafeTransport_refl lens
  have hall : [lp1, lp2].all (fun lp => isSafeTransport lp.lens lens) = true := by
    simp [hs1, hs2]
  simp [glueLocalProofs, hall, hcocycle]

end LensTransport
end ATP
end HeytingLean
