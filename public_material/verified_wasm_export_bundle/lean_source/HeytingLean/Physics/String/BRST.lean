/-!
# BRST complex scaffold (compile-only)

We model a BRST differential `Q` as an endomorphism together with a
property expressing the intended nilpotence `Q ∘ Q = 0`.  The concrete
equation is left abstract at this level so that specialised models can
instantiate `squareZero` with the appropriate law or lemma (for
example, `∀ v, Q (Q v) = 0` once a zero vector is available).
-/

namespace HeytingLean
namespace Physics
namespace String

universe u

structure BRST (V : Type u) where
  Q : V → V
  squareZero : Prop

namespace BRST

variable {V : Type u}

/-- Forget the `squareZero` property, retaining only the underlying
endomorphism.  This is useful in executable contexts that do not need
the proof/law. -/
@[simp] def toEnd (B : BRST V) : V → V := B.Q

end BRST

end String
end Physics
end HeytingLean
