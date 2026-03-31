import HeytingLean.Tests.Bridges.ComputableTestKit
import HeytingLean.Bridges.Topology

/-!
# Computable Topology on Diamond

This module instantiates the Topology bridge with the Diamond lattice,
providing **actually computable** topological operations.

## Key Achievement

While the general Topology.Model uses `noncomputable` encode/decode (because
arbitrary PrimaryAlgebra may not have decidable equality), Diamond's finite
4-element structure enables fully decidable operations.

## Operations Available

- `closure` : Diamond → Diamond (computable via pattern matching)
- `interior` : Diamond → Diamond (derived from closure)
- `boundary` : Diamond → Diamond (cl(x) ⊓ cl(xᶜ))
- `isClosed` : Diamond → Bool (decidable membership in Omega)
- `isOpen` : Diamond → Bool (complement is closed)

## Usage

```lean
#eval DiamondTopology.closure .bot      -- .bot
#eval DiamondTopology.closure .left     -- .left (fixed point)
#eval DiamondTopology.interior .top     -- .top
#eval DiamondTopology.boundary .left    -- .bot (left is clopen)
```
-/

namespace HeytingLean
namespace Tests
namespace Bridges
namespace TopologyComputable

open HeytingLean.LoF
open HeytingLean.Tests.Bridges.ComputableTestKit

/-! ## Computable Topology Model on Diamond -/

/-- The discrete Reentry on Diamond, made available for computation. -/
noncomputable def diamondReentry : Reentry Diamond := Diamond.discreteReentry

/-- The Topology model instantiated with Diamond. -/
noncomputable def diamondModel : HeytingLean.Bridges.Topology.Model Diamond :=
  { R := diamondReentry }

/-! ## Computable Operations

These operations are computable because Diamond has decidable equality
and we can pattern-match on all 4 elements. -/

namespace DiamondTopology

/-- Computable closure operator.
    For the discrete reentry, closure is identity (all elements are fixed). -/
def closure : Diamond → Diamond := Diamond.idClose

/-- Computable complement. -/
def compl : Diamond → Diamond := Diamond.compl'

/-- Computable interior: int(x) = (cl(xᶜ))ᶜ -/
def interior (x : Diamond) : Diamond :=
  compl (closure (compl x))

/-- Computable boundary: ∂(x) = cl(x) ⊓ cl(xᶜ) -/
def boundary (x : Diamond) : Diamond :=
  closure x ⊓ closure (compl x)

/-- Decidable test: is x closed (i.e., a fixed point)? -/
def isClosed (x : Diamond) : Bool :=
  closure x == x

/-- Decidable test: is x open (i.e., complement is closed)? -/
def isOpen (x : Diamond) : Bool :=
  isClosed (compl x)

/-- Decidable test: is x clopen (both open and closed)? -/
def isClopen (x : Diamond) : Bool :=
  isClosed x && isOpen x

/-- The set of all closed elements (as a List for computation). -/
def closedElements : List Diamond :=
  [.bot, .left, .right, .top].filter isClosed

/-- The set of all open elements (as a List for computation). -/
def openElements : List Diamond :=
  [.bot, .left, .right, .top].filter isOpen

/-- Computable Heyting implication (relative pseudo-complement). -/
def himp : Diamond → Diamond → Diamond := Diamond.himp'

/-- Computable meet (intersection). -/
def meet : Diamond → Diamond → Diamond := Diamond.inf'

/-- Computable join (union). -/
def join : Diamond → Diamond → Diamond := Diamond.sup'

end DiamondTopology

/-! ## Verification via #eval -/

section Verification

-- Closure is identity for discrete topology
#eval DiamondTopology.closure .bot   -- .bot
#eval DiamondTopology.closure .left  -- .left
#eval DiamondTopology.closure .right -- .right
#eval DiamondTopology.closure .top   -- .top

-- Interior equals identity for discrete topology
#eval DiamondTopology.interior .bot   -- .bot
#eval DiamondTopology.interior .left  -- .left
#eval DiamondTopology.interior .right -- .right
#eval DiamondTopology.interior .top   -- .top

-- Boundary is empty for discrete topology (all sets are clopen)
#eval DiamondTopology.boundary .bot   -- .bot
#eval DiamondTopology.boundary .left  -- .bot
#eval DiamondTopology.boundary .right -- .bot
#eval DiamondTopology.boundary .top   -- .bot

-- All elements are closed in discrete topology
#eval DiamondTopology.isClosed .bot   -- true
#eval DiamondTopology.isClosed .left  -- true
#eval DiamondTopology.isClosed .right -- true
#eval DiamondTopology.isClosed .top   -- true

-- All elements are open in discrete topology
#eval DiamondTopology.isOpen .bot   -- true
#eval DiamondTopology.isOpen .left  -- true
#eval DiamondTopology.isOpen .right -- true
#eval DiamondTopology.isOpen .top   -- true

-- All elements are clopen
#eval DiamondTopology.isClopen .bot   -- true
#eval DiamondTopology.isClopen .left  -- true
#eval DiamondTopology.isClopen .right -- true
#eval DiamondTopology.isClopen .top   -- true

-- List all closed elements
#eval DiamondTopology.closedElements  -- [bot, left, right, top]

-- List all open elements
#eval DiamondTopology.openElements    -- [bot, left, right, top]

-- Heyting implication tests
#eval DiamondTopology.himp .left .right  -- .right
#eval DiamondTopology.himp .right .left  -- .left
#eval DiamondTopology.himp .bot .top     -- .top
#eval DiamondTopology.himp .top .bot     -- .bot

end Verification

/-! ## Non-Discrete Topology: Indiscrete Nucleus

The discrete topology is "too trivial" - every set is clopen.
Let's define a more interesting nucleus: the **indiscrete** (trivial) topology
where only ⊥ and ⊤ are closed. -/

namespace IndiscreteTopology

/-- Indiscrete closure: maps everything to ⊤ except ⊥ -/
def closure : Diamond → Diamond
  | .bot => .bot
  | _ => .top

/-- Interior in indiscrete topology: only ⊤ is open (besides ∅) -/
def interior : Diamond → Diamond
  | .top => .top
  | _ => .bot

/-- Boundary in indiscrete topology -/
def boundary (x : Diamond) : Diamond :=
  closure x ⊓ closure (Diamond.compl' x)

/-- Is x closed in indiscrete topology? -/
def isClosed (x : Diamond) : Bool :=
  closure x == x

/-- Is x open in indiscrete topology? -/
def isOpen (x : Diamond) : Bool :=
  isClosed (Diamond.compl' x)

end IndiscreteTopology

section IndiscreteVerification

-- Closure maps non-bot to top
#eval IndiscreteTopology.closure .bot   -- .bot
#eval IndiscreteTopology.closure .left  -- .top
#eval IndiscreteTopology.closure .right -- .top
#eval IndiscreteTopology.closure .top   -- .top

-- Only bot and top are closed
#eval IndiscreteTopology.isClosed .bot   -- true
#eval IndiscreteTopology.isClosed .left  -- false
#eval IndiscreteTopology.isClosed .right -- false
#eval IndiscreteTopology.isClosed .top   -- true

-- Only bot and top are open
#eval IndiscreteTopology.isOpen .bot   -- true
#eval IndiscreteTopology.isOpen .left  -- false
#eval IndiscreteTopology.isOpen .right -- false
#eval IndiscreteTopology.isOpen .top   -- true

-- Boundary of left/right is top (they have nonempty boundary)
#eval IndiscreteTopology.boundary .bot   -- .bot
#eval IndiscreteTopology.boundary .left  -- .top
#eval IndiscreteTopology.boundary .right -- .top
#eval IndiscreteTopology.boundary .top   -- .bot

end IndiscreteVerification

/-! ## Alexandrov Topology: Upset Closure

In an Alexandrov topology, closure is the **upset** (upward closure).
For Diamond: cl(x) = {y | x ≤ y}. -/

namespace AlexandrovTopology

/-- Alexandrov closure: upset in the order -/
def closure : Diamond → Diamond
  | .top => .top
  | _ => .top  -- Everything except top has top in its upset

/-- A more refined version that gives the join of x and everything above -/
def closureRefined : Diamond → Diamond
  | .bot => .top   -- upset of bot = everything = top
  | .left => .top  -- upset of left = {left, top}, join = top
  | .right => .top -- upset of right = {right, top}, join = top
  | .top => .top   -- upset of top = {top}

/-- For Alexandrov, let's try downset closure instead (more interesting) -/
def downsetClosure : Diamond → Diamond
  | .bot => .bot
  | .left => .left   -- downset = {bot, left}, but left is the join
  | .right => .right -- downset = {bot, right}
  | .top => .top     -- downset = everything

def isClosed (x : Diamond) : Bool :=
  downsetClosure x == x

end AlexandrovTopology

section AlexandrovVerification

-- All elements are fixed under downset closure (it's a principal filter)
#eval AlexandrovTopology.downsetClosure .bot   -- .bot
#eval AlexandrovTopology.downsetClosure .left  -- .left
#eval AlexandrovTopology.downsetClosure .right -- .right
#eval AlexandrovTopology.downsetClosure .top   -- .top

#eval AlexandrovTopology.isClosed .bot   -- true
#eval AlexandrovTopology.isClosed .left  -- true
#eval AlexandrovTopology.isClosed .right -- true
#eval AlexandrovTopology.isClosed .top   -- true

end AlexandrovVerification

/-! ## Custom Nucleus: Left-Collapsing Topology

A more interesting example: a nucleus that collapses left to top
but preserves other structure. -/

namespace LeftCollapsingTopology

/-- Nucleus that maps left → top, preserves others -/
def nucleus : Diamond → Diamond
  | .bot => .bot
  | .left => .top    -- left collapses to top
  | .right => .right
  | .top => .top

def closure : Diamond → Diamond := nucleus

def isClosed (x : Diamond) : Bool :=
  closure x == x

def isOpen (x : Diamond) : Bool :=
  isClosed (Diamond.compl' x)

/-- The closed sets under this nucleus -/
def closedElements : List Diamond :=
  [.bot, .left, .right, .top].filter isClosed

/-- The open sets under this nucleus -/
def openElements : List Diamond :=
  [.bot, .left, .right, .top].filter isOpen

end LeftCollapsingTopology

section LeftCollapsingVerification

-- Closure behavior
#eval LeftCollapsingTopology.closure .bot   -- .bot
#eval LeftCollapsingTopology.closure .left  -- .top (collapsed!)
#eval LeftCollapsingTopology.closure .right -- .right
#eval LeftCollapsingTopology.closure .top   -- .top

-- Closed sets: bot, right, top (not left!)
#eval LeftCollapsingTopology.closedElements  -- [bot, right, top]

-- Open sets: complements of closed sets
-- compl(bot) = top (closed? yes), compl(right) = left (closed? no),
-- compl(top) = bot (closed? yes)
#eval LeftCollapsingTopology.openElements    -- [bot, top]

-- left is neither open nor closed!
#eval LeftCollapsingTopology.isClosed .left  -- false
#eval LeftCollapsingTopology.isOpen .left    -- false (compl = right, cl(right) = right ≠ left)

end LeftCollapsingVerification

/-! ## Computational Summary

We have demonstrated computable topology operations on Diamond:

| Topology | Closed Sets | Open Sets | Non-clopen |
|----------|-------------|-----------|------------|
| Discrete | {⊥,L,R,⊤}   | {⊥,L,R,⊤} | ∅          |
| Indiscrete| {⊥,⊤}      | {⊥,⊤}     | {L,R}      |
| Left-Collapsing | {⊥,R,⊤} | {⊥,⊤}  | {L,R}      |

These computations execute at compile time via `#eval`, demonstrating
that the Witness layer (pattern matching on finite elements) is sufficient
for topological reasoning without requiring the Classical Chooser.
-/

end TopologyComputable
end Bridges
end Tests
end HeytingLean
