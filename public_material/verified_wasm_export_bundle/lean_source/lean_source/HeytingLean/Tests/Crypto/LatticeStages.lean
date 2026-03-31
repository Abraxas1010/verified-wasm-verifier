import HeytingLean.Crypto.Lattice.Stages

namespace HeytingLean
namespace Tests
namespace Crypto
namespace LatticeStages

open HeytingLean.LoF
open HeytingLean.Crypto.Lattice.Stages

universe u

section
variable {α : Type u} [PrimaryAlgebra α]
variable (R : Reentry α)

-- #check ops and CT lemma
#check ctMeet (R := R)
#check ctJoin (R := R)
#check ctImp  (R := R)
#check opsAtBoolean (R := R)
#check opsAtOrthomodular (R := R)
#check ct_no_branch (R := R)

end

end LatticeStages
end Crypto
end Tests
end HeytingLean

