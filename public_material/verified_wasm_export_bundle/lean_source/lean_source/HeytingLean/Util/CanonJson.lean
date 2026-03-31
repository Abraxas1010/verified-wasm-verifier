import Lean

namespace HeytingLean.Util.CanonJson

open Lean

private def insertSorted (p : String × Json) (xs : List (String × Json)) : List (String × Json) :=
  match xs with
  | [] => [p]
  | q :: qs => if p.fst ≤ q.fst then p :: xs else q :: insertSorted p qs

private def sortPairs : List (String × Json) → List (String × Json)
  | [] => []
  | p :: ps => insertSorted p (sortPairs ps)

/-- Construct a JSON object with keys sorted lexicographically.
    This yields stable, canonical output when combined with `Json.compress`. -/
def mkCanonObj (fields : List (String × Json)) : Json :=
  Json.mkObj (sortPairs fields)

/-- Canonical array wrapper (explicit for symmetry). -/
def mkCanonArr (elems : List Json) : Json :=
  Json.arr (Array.mk elems)

end HeytingLean.Util.CanonJson
