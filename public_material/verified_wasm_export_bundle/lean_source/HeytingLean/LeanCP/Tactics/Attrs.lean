import Lean.LabelAttribute
import Lean.Meta.Tactic.Simp

/-!
# LeanCP Tactic Attributes

Dedicated registration file for tactic-side attributes. Lean cannot use a
freshly declared attribute in the same file, so the attrs live here and the
actual lemma database lives in `SimpLemmas.lean`.
-/

namespace HeytingLean.LeanCP

/-- Simp database consumed by the forward tactics. -/
register_simp_attr leancp_simp

/-- Definitions that forward tactics may unfold aggressively. -/
register_label_attr leancp_unfold

end HeytingLean.LeanCP
