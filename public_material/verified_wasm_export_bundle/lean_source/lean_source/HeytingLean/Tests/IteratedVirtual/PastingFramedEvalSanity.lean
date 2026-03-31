import HeytingLean.IteratedVirtual.PastingFramedEval

namespace HeytingLean
namespace Tests
namespace IteratedVirtual

open HeytingLean.IteratedVirtual

namespace PastingFramedEvalSanity

universe u v w

variable (V : VirtualDoubleCategory.{u, v, w})

-- Compile-only checks that the API is usable without committing to a concrete composition law.
#check PastingFramed.Algebra
#check PastingFramed.eval
#check PastingFramed.algebraOfSubst
#check PastingFramed.eval_bind

end PastingFramedEvalSanity

end IteratedVirtual
end Tests
end HeytingLean

