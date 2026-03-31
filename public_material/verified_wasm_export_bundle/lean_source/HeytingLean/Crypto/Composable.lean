import HeytingLean.Security.Composable.Composition
import HeytingLean.Security.Composable.Instances.IdealKeyExchange
import HeytingLean.Security.Composable.Instances.IdealSecureChannel

/-!
# UC/Composable security (compatibility re-export)

The unified crypto roadmap places the UC scaffold under `HeytingLean.Security.Composable` to avoid
conflicts with `HeytingLean.Constructor.UC` (universal constructor).

Some imported crypto modules (QKD, CT-crypto bundle) expect the namespace
`HeytingLean.Crypto.Composable`. This file provides a thin compatibility layer that re-exports the
Phase 2 UC interface from `HeytingLean.Security.Composable`.
-/

namespace HeytingLean
namespace Crypto
namespace Composable

abbrev IdealFunctionality := HeytingLean.Security.Composable.IdealFunctionality
abbrev Protocol := HeytingLean.Security.Composable.Protocol
abbrev Simulator := HeytingLean.Security.Composable.Simulator
abbrev UCSecure := HeytingLean.Security.Composable.UCSecure

abbrev realExecution {F : IdealFunctionality} (π : Protocol F) :=
  HeytingLean.Security.Composable.realExecution (π := π)

abbrev idealExecution {F : IdealFunctionality} (π : Protocol F) (sim : Simulator F π) :=
  HeytingLean.Security.Composable.idealExecution (π := π) sim

abbrev CompositionKit := HeytingLean.Security.Composable.CompositionKit

abbrev uc_composition
    {F₁ : IdealFunctionality}
    {F₂ : IdealFunctionality}
    (kit : CompositionKit F₁ F₂)
    {π₁ : Protocol F₁} {π₂ : Protocol F₂}
    (h₁ : UCSecure F₁ π₁)
    (h₂ : UCSecure F₂ π₂)
    (h_uses : kit.UsesSubroutine π₂) :=
  HeytingLean.Security.Composable.uc_composition (kit := kit) h₁ h₂ h_uses

namespace Instances

abbrev IdealKeyExchange := HeytingLean.Security.Composable.Instances.IdealKeyExchange
abbrev IdealSecureChannel := HeytingLean.Security.Composable.Instances.IdealSecureChannel

end Instances

end Composable
end Crypto
end HeytingLean
