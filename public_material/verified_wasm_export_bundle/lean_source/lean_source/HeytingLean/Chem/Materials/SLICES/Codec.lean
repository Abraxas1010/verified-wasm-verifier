import HeytingLean.Chem.Materials.SLICES.Syntax
import Mathlib.Data.List.Sort
import Mathlib.Data.String.Basic

/-!
# SLICES: codec (Phase 2)

`encode` renders a labeled quotient graph to a SLICES string.
`decode?` parses a SLICES string back into a labeled quotient graph (existentially quantified size).

Representation:
- prefix: element symbols for nodes in index order (unit cell atoms)
- edges: blocks `u v x y z` where `u v : Nat` are node indices and `(x,y,z) : Int^3` is the
  translation label

Edge ordering:
- Edges are printed in a deterministic sorted order (lex on `(u,v,t)` via the `LinearOrder` instance
  on `Edge n`).
- This is crucial for reproducibility and for canonicalization (Phase 3).
-/

namespace HeytingLean.Chem.Materials.SLICES

open HeytingLean.Chem.PeriodicTable

noncomputable def encode {n : Nat} (g : LabeledQuotientGraph n) : String :=
  let atoms : List String := (List.ofFn g.labels).map symbol
  let edges : List (Edge n) := (g.edges.toList).mergeSort (fun a b => Edge.leBool a b)
  let edgeTokens : List String :=
    edges.flatMap (fun e =>
      [toString e.u.val, toString e.v.val, toString e.t.x, toString e.t.y, toString e.t.z])
  String.intercalate " " (atoms ++ edgeTokens)

def decode? (s : String) : Except String (Sigma LabeledQuotientGraph) := do
  let p ← parse s
  let n := p.atoms.length
  if n = 0 then
    throw "SLICES decode: empty atom list."
  let labels : Fin n → Element := fun i => p.atoms.get i
  let es ← p.edges.mapM (fun re => do
    if hU : re.u < n then
      if hV : re.v < n then
        let u : Fin n := ⟨re.u, hU⟩
        let v : Fin n := ⟨re.v, hV⟩
        return ({ u := u, v := v, t := re.t } : Edge n)
      else
        throw s!"Edge endpoint v out of range: v={re.v}, n={n}"
    else
      throw s!"Edge endpoint u out of range: u={re.u}, n={n}"
    )

  let edges : Finset (Edge n) := es.toFinset
  return ⟨n, { labels := labels, edges := edges }⟩

end HeytingLean.Chem.Materials.SLICES
