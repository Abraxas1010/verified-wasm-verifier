import HeytingLean.LoF.Correspondence.LoFPrimaryClosedSKYBool

/-!
# LoFPrimaryClosedSKYBoolSanity

Sanity checks for the closed-fragment bridge:

`LoFPrimary.Expr 0` (no free variables) → SKY Church booleans,
with a proof that the translation reduces to the canonical boolean.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF
open HeytingLean.LoF.LoFPrimary
open HeytingLean.LoF.Correspondence

open LoFPrimaryClosed

def A0 : LoFPrimary.Expr 0 := Expr.void
def A1 : LoFPrimary.Expr 0 := Expr.mark Expr.void
def A2 : LoFPrimary.Expr 0 := Expr.juxt (Expr.mark Expr.void) Expr.void

#check LoFPrimaryClosed.toSKYBool_correct A0
#check LoFPrimaryClosed.toSKYBool_correct A1
#check LoFPrimaryClosed.toSKYBool_correct A2

end LoF
end Tests
end HeytingLean

