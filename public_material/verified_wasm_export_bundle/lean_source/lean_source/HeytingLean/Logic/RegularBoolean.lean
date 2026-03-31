import HeytingLean.Logic.Booleanization
import Mathlib.Order.BooleanAlgebra

/-!
Boolean algebra structure on `Reg Ω` whenever `Ω` is already a BooleanAlgebra.
This transports the structure along the definitional equality `Reg Ω = Ω`.
-/

namespace HeytingLean
namespace Logic

universe u

instance instBooleanAlgebraReg {Ω : Type u} [BooleanAlgebra Ω] : BooleanAlgebra (Reg Ω) :=
  (inferInstance : BooleanAlgebra Ω)

end Logic
end HeytingLean

