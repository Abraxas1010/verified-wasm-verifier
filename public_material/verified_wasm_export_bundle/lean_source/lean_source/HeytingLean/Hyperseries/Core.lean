import Mathlib.Logic.Hydra
import Mathlib.SetTheory.Surreal.Multiplication

set_option linter.deprecated.module false

namespace HeytingLean
namespace Hyperseries

/-- The surreal corresponding to ordinal `ω`. -/
noncomputable def omegaSurreal : Surreal :=
  (Ordinal.omega0).toSurreal

/--
Abstract target for interpreting hyperseries syntax.
We keep axioms minimal and add laws only when proofs need them.
-/
class HyperserialModel (K : Type*) [CommRing K] where
  omega : K
  exp : K → K
  log : K → K
  hyperExp : Ordinal → K → K
  hyperLog : Ordinal → K → K

end Hyperseries
end HeytingLean
