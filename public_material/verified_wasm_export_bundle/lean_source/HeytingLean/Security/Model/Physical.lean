import HeytingLean.Constructor.CT.Nucleus

namespace HeytingLean
namespace Security
namespace Model

/-!
# Physical security (Constructor Theory-flavored foundations)

We treat a CT impossibility statement (“this task is not possible under a CT nucleus”) as a
primitive notion of physical security.
-/

namespace Physical

/-- CT-style security: the eavesdropping (or other adversarial) task is CT-impossible. -/
def CTSecure {σ : Type u} (J : HeytingLean.Constructor.CT.CTNucleus σ)
    (task : HeytingLean.Constructor.CT.Task σ) : Prop :=
  ¬ HeytingLean.Constructor.CT.CTNucleus.possible (J := J) task

end Physical

end Model
end Security
end HeytingLean
