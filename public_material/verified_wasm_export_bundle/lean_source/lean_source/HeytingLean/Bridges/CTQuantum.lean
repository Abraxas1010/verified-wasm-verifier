import HeytingLean.Constructor.CT.Core
import HeytingLean.Constructor.CT.Nucleus
import HeytingLean.Quantum.Facade

/-
# CT ↔ Quantum bridge (minimal scaffold)

Minimal bridge between CT tasks and the Quantum facade:
* `Model` packages a CT nucleus `J` on tasks over `σ` together with a
  quantum facade over an Ω-carrier;
* `Carrier` is just the facade's `Ω` space, representing quantum
  propositions or effects;
* `encodeClassicalBitCopy` and `encodeQuantumClone` are small helper
  interfaces that allow CT tasks modelling a classical copy or quantum
  cloning attempt to be mapped into the quantum carrier.

This file does *not* prove any no-cloning results; it provides only
enough structure for higher-level CT/quantum adapters and tests to refer
to specific CT tasks in a quantum setting.
-/

namespace HeytingLean
namespace Bridges
namespace CTQuantum

open Constructor
open Constructor.CT
open Quantum

universe u

/-- CT-quantum bridge model: a CT nucleus on tasks over `σ` together
with a quantum facade over an Ω-carrier.  Typeclass instances for `Ω`
are stored inside the structure and re-exposed as instances. -/
structure Model (σ : Type u) (Ω : Type _) where
  [instLE : LE Ω]
  [instOml : Logic.Stage.OmlCore Ω]
  [instHeyting : HeytingAlgebra Ω]
  J  : CTNucleus σ
  QF : Quantum.Facade Ω

attribute [instance] Model.instLE Model.instOml Model.instHeyting

namespace Model

variable {σ : Type u} {Ω : Type _}

/-- Carrier of the CT-quantum model: Ω-level quantum propositions /
effects as seen by the quantum facade. -/
abbrev Carrier (M : Model σ Ω) : Type _ := Ω

/-- A tiny interface for encoding a CT task that acts as a classical
copy operation into the quantum carrier.  Concrete quantum adapters are
expected to implement this for specific substrates. -/
structure ClassicalCopy where
  task : CT.Task σ
  image : Carrier (M := M)

/-- A tiny interface for encoding a CT task that attempts quantum state
cloning into the quantum carrier.  Concrete quantum adapters are
expected to interpret such tasks as forbidden when expressing
no-cloning. -/
structure QuantumClone where
  task : CT.Task σ
  image : Carrier (M := M)

end Model

end CTQuantum
end Bridges
end HeytingLean
