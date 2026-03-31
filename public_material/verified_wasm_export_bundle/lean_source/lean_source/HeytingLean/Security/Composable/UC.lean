import HeytingLean.Security.Composable.Simulator

/-!
# Universal Composability (UC), interface-first: real/ideal paradigm

UC security is modeled as:
- a simulator `S` exists; and
- a chosen indistinguishability predicate holds between the real and ideal executions.

All semantics of "indistinguishable" are left abstract by design.
-/

namespace HeytingLean
namespace Security
namespace Composable

universe u v w

variable {F : IdealFunctionality.{u, v, w}} (π : Protocol F)

/-- Real execution as an experiment producing an output and transcript. -/
def realExecution : F.Input → F.Output × π.Message :=
  fun i =>
    let (o, m, _s') := π.execute i π.init
    (o, m)

/-- Ideal execution (with simulator) as an experiment producing an output and transcript. -/
def idealExecution (sim : Simulator F π) : F.Input → F.Output × π.Message :=
  fun i =>
    let (o, leak) := F.compute i
    let (m, _s') := sim.simulate leak sim.init
    (o, m)

/-- UC security: there exists a simulator and an indistinguishability notion relating
`realExecution` and `idealExecution`. -/
def UCSecure (F : IdealFunctionality.{u, v, w}) (π : Protocol F) : Prop :=
  ∃ sim : Simulator F π,
    ∃ Indistinguishable :
        (F.Input → F.Output × π.Message) → (F.Input → F.Output × π.Message) → Prop,
      Indistinguishable (realExecution π) (idealExecution π sim)

end Composable
end Security
end HeytingLean
