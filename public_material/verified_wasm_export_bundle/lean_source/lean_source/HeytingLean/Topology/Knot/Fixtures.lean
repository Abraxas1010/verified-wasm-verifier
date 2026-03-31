import HeytingLean.Topology.Knot.Braid
import HeytingLean.Topology.Knot.Burau

/-!
# Knot fixtures (braid words)

Small canonical fixtures used for regression tests and CLI demos.

We store expected Alexander polynomials in a normalization that is stable up to multiplication
by units `±t^k` (shift + sign). References are recorded inline for provenance.
-/

namespace HeytingLean
namespace Topology
namespace Knot

open HeytingLean.Topology.Knot
open HeytingLean.Topology.Knot.Braid
open HeytingLean.Topology.Knot.Burau

namespace Fixtures

abbrev Poly := LaurentPoly

private def normalizeUpToUnit (p : Poly) : Poly :=
  if p = 0 then
    0
  else
    let ts := p.toList
    let minE := (ts.head!).1
    let shifted : Poly :=
      { terms := ts.map (fun (e, c) => (e - minE, c)) }
    -- Make the leading coefficient positive (canonical sign).
    match shifted.toList with
    | [] => 0
    | (_, c0) :: _ =>
        if c0 < 0 then -shifted else shifted

structure BraidFixture where
  name : String
  strands : Nat
  gens : List Braid.Gen
  expectedAlex : Poly
  reference : String
deriving Repr

def unknot : BraidFixture :=
  { name := "unknot"
    strands := 1
    gens := []
    expectedAlex := 1
    reference := "Alexander polynomial of the unknot is 1 (standard normalization)."
  }

def unlink2 : BraidFixture :=
  { name := "unlink2"
    strands := 2
    gens := []
    expectedAlex := 0
    reference := "Split 2-component unlink has 0 single-variable Alexander polynomial under the Burau closure formula."
  }

def hopfPos : BraidFixture :=
  { name := "hopf_pos"
    strands := 2
    gens := [{ i := 0, sign := .pos }, { i := 0, sign := .pos }]
    -- This computes to `1 - t` (already normalized up to units).
    expectedAlex := normalizeUpToUnit { terms := [(0, 1), (1, -1)] }
    reference := "Hopf link braid word σ1^2. See e.g. Wikipedia Hopf link page for braid word."
  }

def trefoilPos : BraidFixture :=
  { name := "trefoil_pos"
    strands := 2
    gens := [{ i := 0, sign := .pos }, { i := 0, sign := .pos }, { i := 0, sign := .pos }]
    -- Wikipedia often reports Δ(t)=t-1+t^{-1}; normalized up to units this is `1 - t + t^2`.
    expectedAlex := normalizeUpToUnit { terms := [(0, 1), (1, -1), (2, 1)] }
    reference := "Trefoil: Δ(t)=t-1+t^{-1}; Conway ∇(z)=z^2+1 (see Wikipedia trefoil / knot polynomial tables)."
  }

def figureEight : BraidFixture :=
  { name := "figure_eight"
    strands := 3
    gens := [{ i := 0, sign := .pos }, { i := 1, sign := .neg }, { i := 0, sign := .pos }, { i := 1, sign := .neg }]
    -- Wikipedia/MathWorld often report Δ(t) = -t + 3 - t^{-1}; normalized up to units this is `1 - 3t + t^2`.
    expectedAlex := normalizeUpToUnit { terms := [(0, 1), (1, -3), (2, 1)] }
    reference := "Figure-eight braid word σ1 σ2^{-1} σ1 σ2^{-1}; Δ(t) = -t + 3 - t^{-1} (see Wikipedia/MathWorld)."
  }

def braidFixtures : List BraidFixture :=
  [unknot, unlink2, hopfPos, trefoilPos, figureEight]

def alexanderExpected (f : BraidFixture) : Poly :=
  f.expectedAlex

def alexanderComputed (f : BraidFixture) : Except String Poly :=
  (Burau.alexanderOfClosedBraid f.strands f.gens).map normalizeUpToUnit

end Fixtures

end Knot
end Topology
end HeytingLean

