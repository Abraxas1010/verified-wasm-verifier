import HeytingLean.Tests.KernelAssurance.Fixture

namespace HeytingLean.Tests.KernelAssurance.Surface

open HeytingLean.KernelAssurance
open HeytingLean.Tests.KernelAssurance

example : familyOfDecl theoremDecl = .theorem := rfl
example : statusOfDecl theoremDecl = .supported := rfl
example : familyOfDecl axiomDecl = .axiom := rfl
example : statusOfDecl axiomDecl = .blocked := rfl

end HeytingLean.Tests.KernelAssurance.Surface
