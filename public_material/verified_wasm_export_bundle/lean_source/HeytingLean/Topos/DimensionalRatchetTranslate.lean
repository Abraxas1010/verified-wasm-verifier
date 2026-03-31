import HeytingLean.Topos.DimensionalRatchet
import HeytingLean.Quantum.Translate.Omega

/-!
# Dimensional Ratchet: a concrete OML → Heyting transport (via translation)

`HeytingLean.Topos.DimensionalRatchet` intentionally records the “OML → Heyting” part of the
ratchet as an *interface* (because a fully general Sasaki-fixed-point Heytingification is subtle).

This file supplies a concrete, already-mechanized construction from the repo’s translation layer:

* Choose a target frame `α`.
* Provide a `HeytingLean.Quantum.Translate.QLMap β α` from an orthomodular lattice `β` into `α`
  together with its associated modality `T.M : Modality α`.
* Take the Heyting carrier to be `Ω_{T.M}` (fixed points of the modality nucleus), i.e.
  `HeytingLean.Quantum.Translate.Omega T.M`.

This “transport” is the right level for the project’s narrative: it makes the constructive core
explicit, and it reuses the existing Sasaki→Heyting bridge lemmas living in the translation layer.
-/

namespace HeytingLean
namespace Topos
namespace DimensionalRatchet

open HeytingLean.Quantum
open HeytingLean.Quantum.Translate

namespace Interface

open HeytingLean.Quantum.OML

/-- Build an `OMLToHeyting` transport from a translation `QLMap` into a frame, taking
the Heyting carrier to be the fixed-point sublocale `Ω_{T.M}`. -/
noncomputable def omlToHeyting_ofTranslate
    {β : Type _} {α : Type _}
    [OrthocomplementedLattice β] [OrthomodularLattice β]
    [Order.Frame α]
    (T : QLMap β α) : OMLToHeyting β where
  H := Omega T.M

/-- In the translated Heyting core `Ω_{T.M}`, the (closed) translated Sasaki hook lies below
the Heyting implication, re-exported from `HeytingLean.Quantum.Translate.Omega`. -/
theorem sasakiHook_le_himp_in_omega
    {β : Type _} {α : Type _}
    [OrthocomplementedLattice β] [OrthomodularLattice β]
    [Order.Frame α] [HasCompl α]
    (T : QLMap β α) [QLMap.ComplPreserving T] (a b : β) :
    HeytingLean.Quantum.Translate.Omega.mk (M := T.M) (T.M.J (T.tr (OML.sasakiHook a b))) (by simp)
      ≤
      HeytingLean.Quantum.Translate.Omega.mk (M := T.M) (T.M.J ((T.tr a)ᶜ ⊔ T.tr b)) (by simp) := by
  simpa using (Omega.sasakiHook_le_himp (T := T) (a := a) (b := b))

end Interface

end DimensionalRatchet
end Topos
end HeytingLean
