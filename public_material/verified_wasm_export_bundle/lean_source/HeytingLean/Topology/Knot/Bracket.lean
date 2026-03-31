import Std
import HeytingLean.Topology.Knot.PlanarDiagram
import HeytingLean.Topology.Knot.PDGraph
import HeytingLean.Topology.Knot.LaurentPoly

/-!
# Knot theory: Kauffman bracket (toy, executable)

This module implements the **Kauffman bracket** ⟨D⟩ as a computable recursion on a
PD-style planar diagram encoding.

Scope:
- Executable bracket polynomial over Laurent polynomials `ℤ[A, A⁻¹]` (here: `Int[T;T⁻¹]`).
- Works for small diagrams; complexity is exponential in the number of crossings.
- Reidemeister move theory is implemented in `HeytingLean.Topology.Knot.Reidemeister`.

Definition (one standard convention):
- ⟨O⟩ = 1 for the unknot.
- ⟨D ⊔ O⟩ = d · ⟨D⟩ where `d = -A^2 - A^{-2}`.
- Skein relation at a crossing: `⟨×⟩ = A · ⟨A-smoothing⟩ + A⁻¹ · ⟨B-smoothing⟩`.

We compute ⟨D⟩ by repeatedly smoothing the **last crossing** and recursively evaluating the
resulting diagram, using a label-free `PDGraph` representation internally.
-/

namespace HeytingLean
namespace Topology
namespace Knot

open Std

namespace Kauffman

abbrev Poly := LaurentPoly

private def mon (k : Int) : Poly :=
  LaurentPoly.mon k 1

/-- The Kauffman bracket parameter `A` as a Laurent monomial. -/
def A : Poly :=
  mon 1

/-- The Laurent monomial `A⁻¹`. -/
def Ainv : Poly :=
  mon (-1)

/-- The Kauffman bracket loop factor `d = -A^2 - A^{-2}`. -/
def d : Poly :=
  -(mon 2) - (mon (-2))

private def smoothLastCore! (freeLoops : Nat) (n : Nat) (arcNbr : Array Nat) (isB : Bool) :
    (Nat × Array Nat) := Id.run do
  -- Precondition: `n > 0` and `arcNbr` is a valid involution of length `4*n`.
  let m := 4 * n
  let base := m - 4

  let smooth (idx : Nat) : Nat :=
    let pos := idx % 4
    if isB then
      match pos with
      | 0 => base + 3
      | 1 => base + 2
      | 2 => base + 1
      | _ => base + 0
    else
      match pos with
      | 0 => base + 1
      | 1 => base + 0
      | 2 => base + 3
      | _ => base + 2

  let isRemoved (idx : Nat) : Bool :=
    idx >= base

  let exitFromExternal (x : Nat) : Nat := Id.run do
    let mut r := arcNbr[x]!
    for _ in [0:4] do
      let r' := smooth r
      let y := arcNbr[r']!
      if y < base then
        return y
      r := y
    -- should be unreachable for well-formed inputs
    return x

  -- Count new free loops created entirely inside the removed region.
  let mut visited : Array Bool := Array.replicate 4 false
  let mut deltaLoops := 0
  for off in [0:4] do
    if !visited[off]! then
      let start := base + off
      let mut stack : List Nat := [start]
      let mut touchesExternal := false
      while !stack.isEmpty do
        match stack with
        | [] => pure ()
        | v :: rest => do
            stack := rest
            if isRemoved v then
              let vOff := v - base
              if vOff < 4 && !visited[vOff]! then
                visited := visited.set! vOff true
                let a := arcNbr[v]!
                if a < base then
                  touchesExternal := true
                else
                  stack := a :: stack
                let s := smooth v
                stack := s :: stack
            pure ()
      if !touchesExternal then
        deltaLoops := deltaLoops + 1

  -- Rewire external endpoints that used to connect to the removed region.
  let mut newNbr : Array Nat := arcNbr.take base
  for x in [0:base] do
    let p := arcNbr[x]!
    if isRemoved p then
      let y := exitFromExternal x
      newNbr := newNbr.set! x y
      newNbr := newNbr.set! y x

  return (freeLoops + deltaLoops, newNbr)

private def bracketCore (freeLoops : Nat) : Nat → Array Nat → Poly
  | 0, _ =>
      if freeLoops = 0 then
        1
      else
        d ^ (freeLoops - 1)
  | Nat.succ n', arcNbr =>
      let (freeA, nbrA) := smoothLastCore! freeLoops (Nat.succ n') arcNbr false
      let (freeB, nbrB) := smoothLastCore! freeLoops (Nat.succ n') arcNbr true
      (A * bracketCore freeA n' nbrA) + (Ainv * bracketCore freeB n' nbrB)

def bracketGraph (g : PDGraph) : Except String Poly := do
  PDGraph.validate g
  return bracketCore g.freeLoops g.n g.arcNbr

/-- Compute the Kauffman bracket ⟨D⟩ for a PD diagram. -/
def bracket (dgm : PlanarDiagram) : Except String Poly := do
  let g ← PDGraph.ofPlanarDiagram dgm
  bracketGraph g

end Kauffman

end Knot
end Topology
end HeytingLean
