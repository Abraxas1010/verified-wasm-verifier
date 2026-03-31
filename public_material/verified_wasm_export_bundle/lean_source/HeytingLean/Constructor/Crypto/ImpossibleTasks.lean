import HeytingLean.Constructor.CT.TaskExistence

/-!
# Crypto-flavored CT task names (interface-first)

This file is intentionally lightweight: it provides *names* and small packaging structures for
cryptography-relevant tasks (eavesdropping, cloning) in the constructor-existence CT layer.

Concrete instantiations (BB84/E91, authenticated channels, etc.) supply the actual tasks.
-/

namespace HeytingLean
namespace Constructor
namespace Crypto

open HeytingLean.Constructor.CT

universe u

variable {σ : Type u}

/-- A named “bad” task: typically an eavesdropping/intercept task. -/
structure BadTask (σ : Type u) where
  task : HeytingLean.Constructor.CT.Task σ

/-- A named “cloning” task. Protocol-specific developments instantiate this appropriately. -/
structure CloningTask (σ : Type u) where
  task : HeytingLean.Constructor.CT.Task σ

/-- A reduction premise packaging: success at `attack` would entail ability to perform `clone`. -/
structure AttackRequiresCloning (σ : Type u) where
  attack : BadTask σ
  clone : CloningTask σ

end Crypto
end Constructor
end HeytingLean
