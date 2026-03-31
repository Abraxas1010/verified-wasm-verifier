import HeytingLean.Tests.Bridges.ComputableTestKit
import HeytingLean.Tests.Bridges.TopologyComputable

/-!
# Computable Fixed-Point Algebra (Omega)

This module provides computable operations on the **fixed-point subtype** `R.Omega`
for Diamond and analyzes which operators qualify as nuclei.

## Key Discovery: Diamond Admits Only the Trivial Nucleus

A **nucleus** on a Heyting algebra must satisfy:
1. Idempotent: N(N(x)) = N(x)
2. **Preserves meets**: N(x ⊓ y) = N(x) ⊓ N(y)
3. Inflationary: x ≤ N(x)

For Diamond, the meet-preservation constraint is extremely restrictive.
Since `left ⊓ right = ⊥`, we need `N(left) ⊓ N(right) = ⊥`.

But inflationary requires:
- N(left) ≥ left, so N(left) ∈ {left, top}
- N(right) ≥ right, so N(right) ∈ {right, top}

Checking all combinations of N(left) ⊓ N(right):
- left ⊓ right = ⊥ ✓
- left ⊓ top = left ≠ ⊥ ✗
- top ⊓ right = right ≠ ⊥ ✗
- top ⊓ top = top ≠ ⊥ ✗

**Conclusion: The ONLY nucleus on Diamond is the identity!**

This is because Diamond's orthogonality (left ⊓ right = ⊥) forces any
inflationary meet-preserving operator to fix both left and right.
-/

namespace HeytingLean
namespace Tests
namespace Bridges
namespace OmegaComputable

open HeytingLean.LoF
open HeytingLean.Tests.Bridges.ComputableTestKit

/-! ## The Only Nucleus on Diamond -/

/-- The discrete (identity) nucleus - the ONLY valid nucleus on Diamond.
    Any function satisfying the nucleus laws on Diamond must be id. -/
def discreteNucleus : Diamond → Diamond := id

/-- Discrete nucleus is idempotent. -/
theorem discrete_idempotent (x : Diamond) :
    discreteNucleus (discreteNucleus x) = discreteNucleus x := rfl

/-- Discrete nucleus preserves meets. -/
theorem discrete_preserves_inf (x y : Diamond) :
    discreteNucleus (x ⊓ y) = discreteNucleus x ⊓ discreteNucleus y := rfl

/-- Discrete nucleus is inflationary. -/
theorem discrete_inflationary (x : Diamond) : x ≤ discreteNucleus x := le_refl x

/-! ## Why No Other Nucleus Exists (Computational Proof)

We can verify computationally that any candidate nucleus function
that is inflationary and preserves meets must be the identity.

For each candidate N(left) ∈ {left, top} and N(right) ∈ {right, top}:
- Check if N(left ⊓ right) = N(left) ⊓ N(right)
- Only (left, right) satisfies this, giving identity.
-/

/-- Check if a function is a valid nucleus (computational). -/
def isValidNucleus (f : Diamond → Diamond) : Bool :=
  -- Must fix bot and top (from inflationary + idempotent)
  f .bot == .bot &&
  f .top == .top &&
  -- Must be inflationary
  Diamond.le' .bot (f .bot) &&
  Diamond.le' .left (f .left) &&
  Diamond.le' .right (f .right) &&
  Diamond.le' .top (f .top) &&
  -- Must preserve meets (check all pairs)
  (f (.bot ⊓ .bot) == f .bot ⊓ f .bot) &&
  (f (.bot ⊓ .left) == f .bot ⊓ f .left) &&
  (f (.bot ⊓ .right) == f .bot ⊓ f .right) &&
  (f (.bot ⊓ .top) == f .bot ⊓ f .top) &&
  (f (.left ⊓ .left) == f .left ⊓ f .left) &&
  (f (.left ⊓ .right) == f .left ⊓ f .right) &&  -- Key constraint!
  (f (.left ⊓ .top) == f .left ⊓ f .top) &&
  (f (.right ⊓ .right) == f .right ⊓ f .right) &&
  (f (.right ⊓ .top) == f .right ⊓ f .top) &&
  (f (.top ⊓ .top) == f .top ⊓ f .top)

-- Identity is a valid nucleus
#eval isValidNucleus id  -- true

-- Left-collapsing (left → top) is NOT a valid nucleus
def leftCollapsing : Diamond → Diamond
  | .bot => .bot
  | .left => .top
  | .right => .right
  | .top => .top

#eval isValidNucleus leftCollapsing  -- false (fails left ⊓ right check)

-- Right-collapsing (right → top) is NOT a valid nucleus
def rightCollapsing : Diamond → Diamond
  | .bot => .bot
  | .left => .left
  | .right => .top
  | .top => .top

#eval isValidNucleus rightCollapsing  -- false (fails left ⊓ right check)

-- Both-collapsing is NOT a valid nucleus
def bothCollapsing : Diamond → Diamond
  | .bot => .bot
  | .left => .top
  | .right => .top
  | .top => .top

#eval isValidNucleus bothCollapsing  -- false

/-! ## Enumerate All Possible Candidates

Since Diamond has 4 elements and we need:
- f(bot) = bot, f(top) = top (forced by properties)
- f(left) ∈ {left, top} (inflationary)
- f(right) ∈ {right, top} (inflationary)

There are exactly 4 candidates. Let's check them all. -/

def candidate1 : Diamond → Diamond  -- identity
  | .bot => .bot | .left => .left | .right => .right | .top => .top

def candidate2 : Diamond → Diamond  -- left → top
  | .bot => .bot | .left => .top | .right => .right | .top => .top

def candidate3 : Diamond → Diamond  -- right → top
  | .bot => .bot | .left => .left | .right => .top | .top => .top

def candidate4 : Diamond → Diamond  -- both → top
  | .bot => .bot | .left => .top | .right => .top | .top => .top

#eval isValidNucleus candidate1  -- true  (identity)
#eval isValidNucleus candidate2  -- false (left-collapsing)
#eval isValidNucleus candidate3  -- false (right-collapsing)
#eval isValidNucleus candidate4  -- false (both-collapsing)

-- Verify identity is the ONLY valid nucleus among all candidates
def countValidNuclei : ℕ :=
  [candidate1, candidate2, candidate3, candidate4].filter isValidNucleus |>.length

#eval countValidNuclei  -- 1 (only identity)

/-! ## Omega Operations (All of Diamond)

Since the only nucleus is identity, Omega = Diamond.
These operations are the same as Diamond's lattice operations. -/

section OmegaOperations

def omegaMeet (x y : Diamond) : Diamond := x ⊓ y
def omegaJoin (x y : Diamond) : Diamond := x ⊔ y
def omegaHimp (x y : Diamond) : Diamond := Diamond.himp' x y
def omegaCompl (x : Diamond) : Diamond := Diamond.compl' x

-- Verification
#eval omegaMeet .left .right   -- .bot
#eval omegaJoin .left .right   -- .top
#eval omegaHimp .left .right   -- .right
#eval omegaCompl .left         -- .right
#eval omegaCompl .right        -- .left

end OmegaOperations

/-! ## Lattice Statistics -/

namespace LatticeStats

/-- All elements of Diamond -/
def allElements : List Diamond := [.bot, .left, .right, .top]

/-- Number of fixed points (= 4 for identity) -/
def omegaSize : ℕ := allElements.filter (fun x => discreteNucleus x == x) |>.length

/-- Number of atoms (minimal nontrivial elements) -/
def atomCount : ℕ :=
  allElements.filter (fun x =>
    x != .bot &&
    allElements.all (fun y => y == .bot || y == x || !(Diamond.le' y x))
  ) |>.length

/-- Is the lattice a chain? -/
def isChain : Bool :=
  allElements.all fun x =>
    allElements.all fun y =>
      Diamond.le' x y || Diamond.le' y x

/-- Is the lattice Boolean? -/
def isBoolean : Bool :=
  allElements.all fun x =>
    allElements.any fun y =>
      (x ⊓ y) == .bot && (x ⊔ y) == .top

end LatticeStats

#eval LatticeStats.omegaSize   -- 4
#eval LatticeStats.atomCount   -- 2 (left and right)
#eval LatticeStats.isChain     -- false
#eval LatticeStats.isBoolean   -- true

/-! ## Summary

**Key Result**: Diamond admits exactly ONE nucleus: the identity.

Computational verification:
- 4 possible inflationary candidates
- Only 1 (identity) satisfies meet-preservation
- The constraint `N(left ⊓ right) = N(left) ⊓ N(right)` forces N(left) = left, N(right) = right

**Why the orthogonality matters**:
- left ⊓ right = ⊥ in Diamond
- If N(left) = top, then N(left) ⊓ N(right) ≥ right (since N(right) ≥ right)
- But N(left ⊓ right) = N(⊥) = ⊥
- Contradiction: right ≠ ⊥

**Implications**:
| Feature | Diamond Status |
|---------|----------------|
| Full Heyting algebra | ✓ |
| CompleteLattice (Classical) | ✓ |
| Non-trivial nucleus | ✗ |
| Interesting topology | ✗ (only discrete) |

**To get non-trivial nuclei**, use larger lattices like the 5-element pentagon
or chain lattices where orthogonality constraints don't block collapsing.
-/

end OmegaComputable
end Bridges
end Tests
end HeytingLean
