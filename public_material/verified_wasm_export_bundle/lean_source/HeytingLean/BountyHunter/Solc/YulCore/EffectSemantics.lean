import HeytingLean.BountyHunter.Solc.YulCore.Types
import HeytingLean.BountyHunter.Solc.YulTextMini.EffectSemantics

/-!
# HeytingLean.BountyHunter.Solc.YulCore.EffectSemantics

Phase-1 bootstrap: interpret `YulCore` programs in an **effect-only** semantics.

This is intentionally weaker than full Yul semantics, but it is the piece we
already use for security checks like CEI/dominance, and it is the first
observer we can connect to concrete EVM traces via certificates.
-/

namespace HeytingLean.BountyHunter.Solc.YulCore

abbrev EffState := HeytingLean.BountyHunter.Solc.YulTextMini.EffState

abbrev evalStmt := HeytingLean.BountyHunter.Solc.YulTextMini.evalStmt
abbrev evalStmts := HeytingLean.BountyHunter.Solc.YulTextMini.evalStmts

end HeytingLean.BountyHunter.Solc.YulCore
