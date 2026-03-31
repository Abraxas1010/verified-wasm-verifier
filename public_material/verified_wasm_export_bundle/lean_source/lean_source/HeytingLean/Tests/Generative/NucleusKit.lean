import HeytingLean.Generative.NucleusKit

namespace HeytingLean
namespace Tests
namespace Generative
namespace NucleusKit

open HeytingLean.Generative

universe u

section
variable {α : Type u} [PrimaryAlgebra α]
variable (R : HeytingLean.LoF.Reentry α)

#check Generative.NucleusKit.birth (R := R)
#check Generative.NucleusKit.occam (R := R)
#check Generative.NucleusKit.synth (R := R)
#check Generative.NucleusKit.occam_idem (R := R)

end

end NucleusKit
end Generative
end Tests
end HeytingLean

