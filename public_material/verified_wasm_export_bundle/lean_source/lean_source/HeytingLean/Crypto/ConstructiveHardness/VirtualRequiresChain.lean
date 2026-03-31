import HeytingLean.Util.VirtualChain
import HeytingLean.Crypto.ConstructiveHardness.Composition

/-!
# Crypto.ConstructiveHardness.VirtualRequiresChain

Systematic reuse of the “virtualization via chains” pattern for CT task reductions:

- A one-step “requires” edge is a function `CT.possible T₁ → CT.possible T₂`.
- A multi-step reduction is a `VirtualChain` of such edges.
- You can *compile* the chain into a single implication by function composition.

This provides an audit-trail-friendly alternative to directly proving a single “big” implication.
-/

namespace HeytingLean
namespace Crypto
namespace ConstructiveHardness

open HeytingLean.Constructor.CT
open HeytingLean.Util

universe u

namespace RequiresChain

variable {σ : Type u} {CT : TaskCT σ}

def Step (CT : TaskCT σ) (T U : HeytingLean.Constructor.CT.Task σ) : Prop :=
  CT.possible T → CT.possible U

abbrev Chain (CT : TaskCT σ) (T U : HeytingLean.Constructor.CT.Task σ) : Type u :=
  VirtualChain (Step CT) T U

def compile {T U : HeytingLean.Constructor.CT.Task σ} :
    Chain CT T U → (CT.possible T → CT.possible U)
  | .nil _ => fun h => h
  | .cons h rest => fun hT => compile rest (h hT)

theorem composed_security
    {T_attack T_sub : HeytingLean.Constructor.CT.Task σ}
    (p : Chain CT T_attack T_sub)
    (h_sub_impossible : CT.impossible T_sub) :
    CT.impossible T_attack := by
  intro hPossible
  exact h_sub_impossible (compile p hPossible)

end RequiresChain

end ConstructiveHardness
end Crypto
end HeytingLean
