import HeytingLean.Topos.JRatchet

namespace HeytingLean
namespace Tests
namespace Topos

/-! Smoke checks for the `JRatchet` wrapper layer. -/

open Order

section
  -- A concrete ambient frame to instantiate the closure formulas.
  abbrev X : Type := Set Bool

  -- `Set Bool` is a complete Boolean algebra, hence a frame.
  instance : Order.Frame X := by infer_instance

  noncomputable abbrev dnNucleus : Nucleus X :=
    HeytingLean.Topos.JRatchet.doubleNegNucleus X

  -- The fixed-point sublocale exists and is a frame/Heyting algebra (mathlib).
  #check dnNucleus.toSublocale
  #check (by infer_instance : HeytingAlgebra dnNucleus.toSublocale)
  #check (by infer_instance : Order.Frame dnNucleus.toSublocale)

  -- The paper-facing “closed join/sup” formulas are available.
  #check HeytingLean.Topos.JRatchet.coe_restrict_toSublocale (n := dnNucleus)
  #check HeytingLean.Topos.JRatchet.sup_eq_restrict (n := dnNucleus)
  #check HeytingLean.Topos.JRatchet.coe_sup (n := dnNucleus)
  #check HeytingLean.Topos.JRatchet.iSup_eq_restrict (n := dnNucleus)
  #check HeytingLean.Topos.JRatchet.coe_iSup (n := dnNucleus)

  -- Minimal sanity: `coe_sup` rewrites join in the fixed-point core to closure of ambient join.
  example (a b : dnNucleus.toSublocale) :
      ((a ⊔ b : dnNucleus.toSublocale) : X) = dnNucleus ((a : X) ⊔ (b : X)) :=
    HeytingLean.Topos.JRatchet.coe_sup (n := dnNucleus) a b
end

section
  -- Guardrail: explicit non-distributive lattice counterexample.
  #check HeytingLean.Topos.JRatchet.Guardrails.M3
  #check HeytingLean.Topos.JRatchet.Guardrails.M3.not_distrib
end

end Topos
end Tests
end HeytingLean
