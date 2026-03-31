import Mathlib.Logic.Basic

/-!
# Physical modality (constructor-theoretic polarity)

Constructor Theory uses a notion of “possible” that is **stronger** than mere logical truth:
if a task is physically possible, then (in particular) the corresponding specification is
logically satisfiable / realizable.

Therefore, at the level of propositions, the correct polarity is:

    PhysPossible P  →  P

This is **not** a Mathlib `Nucleus Prop` (which is a closure operator and thus inflationary,
`P → R P`). Instead we model the physical layer as an abstract modality on `Prop` that is
sound and monotone w.r.t. implication.

This file is intentionally minimal and extractable.
-/

namespace HeytingLean
namespace Crypto
namespace ConstructiveHardness

/-- A “physical possibility” modality on propositions.

Interpretation: `Φ P` means “P is physically realizable / constructible / achievable by some
constructor”, and we require:
* **soundness**: if physically realizable then true (`Φ P → P`);
* **monotonicity**: if `P → Q` then `Φ P → Φ Q` (achieving P also achieves any consequence Q).

No other laws (idempotence, meet preservation, etc.) are assumed at this layer.

Example (informal): in a quantum-mechanical instantiation, `Φ P` might mean
“there exists a preparation + measurement procedure that achieves specification `P`”, and
`sound` would be justified by the operational semantics of that model.
-/
structure PhysicalModality where
  toFun : Prop → Prop
  mono : ∀ {P Q : Prop}, (P → Q) → (toFun P → toFun Q)
  sound : ∀ {P : Prop}, toFun P → P

namespace PhysicalModality

variable (Φ : PhysicalModality)

@[simp] lemma not_toFun_of_not {P : Prop} : (¬ P) → ¬ Φ.toFun P := by
  intro hNotP hΦP
  exact hNotP (Φ.sound hΦP)

end PhysicalModality

end ConstructiveHardness
end Crypto
end HeytingLean
