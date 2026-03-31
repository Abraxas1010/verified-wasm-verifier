import HeytingLean.Numbers.Surreal.QuotCoreSemantics

namespace HeytingLean.Tests.Numbers.SurrealQuotCoreSemantics

open HeytingLean.Numbers.Surreal

noncomputable section

variable (x y z : SurrealQ)

example :
    canonicalizeQ zeroQCore = zeroQCore := by
  simp

example :
    canonicalizeQ (addQCore x y) = addQCore x y := by
  simp

example :
    canonicalizeQ (negQCore x) = negQCore x := by
  simp

example :
    canonicalizeQ (mulQCore x y) = mulQCore x y := by
  simp

example :
    toIGameQ (addQCore x y) = toIGameQ x + toIGameQ y := by
  exact toIGameQ_addQCore x y

example :
    toIGameQ (negQCore x) = -toIGameQ x := by
  exact toIGameQ_negQCore x

example :
    toIGameQ (mulQCore x y) = toIGameQ x * toIGameQ y := by
  exact toIGameQ_mulQCore x y

example :
    toIGameQ zeroQCore = 0 := by
  exact toIGameQ_zeroQCore

example :
    toIGameQ (mulQCore zeroQCore x) = 0 := by
  exact toIGameQ_mul_zeroQCore_left x

example :
    toIGameQ (mulQCore x zeroQCore) = 0 := by
  exact toIGameQ_mul_zeroQCore_right x

example :
    toIGameQ (addQCore zeroQCore x) = toIGameQ x := by
  exact toIGameQ_add_zeroQCore_left x

example :
    toIGameQ (addQCore x zeroQCore) = toIGameQ x := by
  exact toIGameQ_add_zeroQCore_right x

example :
    toIGameQ (mulQCore x (addQCore y z)) ≈
      toIGameQ (addQCore (mulQCore x y) (mulQCore x z)) := by
  exact toIGameQ_mul_addQCore_equiv x y z

example :
    toIGameQ (mulQCore (addQCore x y) z) ≈
      toIGameQ (addQCore (mulQCore x z) (mulQCore y z)) := by
  exact toIGameQ_add_mulQCore_equiv x y z

example :
    toIGameQ (mulQCore (mulQCore x y) z) ≈
      toIGameQ (mulQCore x (mulQCore y z)) := by
  exact toIGameQ_mulQCore_assoc_equiv x y z

example :
    toIGameQ (mulQCore x y) = toIGameQ (mulQCore y x) := by
  exact toIGameQ_mulQCore_comm x y

example :
    toIGameQ (addQCore x y) = toIGameQ (addQCore y x) := by
  exact toIGameQ_addQCore_comm x y

example :
    toIGameQ (addQCore (addQCore x y) z) = toIGameQ (addQCore x (addQCore y z)) := by
  exact toIGameQ_addQCore_assoc x y z

example :
    toIGameQ (addQCore (negQCore x) x) ≈ 0 := by
  exact toIGameQ_add_left_negQCore_equiv_zero x

example :
    toIGameQ (addQCore x (negQCore x)) ≈ 0 := by
  exact toIGameQ_add_right_negQCore_equiv_zero x

example :
    toIGameQ (addQCore (negQCore x) (addQCore x y)) ≈ toIGameQ y := by
  exact toIGameQ_add_left_cancelQCore_equiv x y

example :
    toIGameQ (addQCore x (addQCore (negQCore x) y)) ≈ toIGameQ y := by
  exact toIGameQ_add_right_cancelQCore_equiv x y

end

end HeytingLean.Tests.Numbers.SurrealQuotCoreSemantics
