import HeytingLean.Physics.LFTBridge
import HeytingLean.Physics.SubstrateBridge

namespace HeytingLean.Physics

-- Central surface for the physics ecosystem integration. For now we only expose
-- the stacks that currently build on Lean 4.25.0 without vendor patches.
-- PhysLean is optional (blocked upstream) and QuantumInfo is temporarily
-- disabled until the `Star`/`LinearMap.adjoint_inner_right` regressions are
-- fixed on their main branch. Substrate + LFT stay enabled.

end HeytingLean.Physics
