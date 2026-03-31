import HeytingLean.LoF.ICC.Syntax

namespace HeytingLean
namespace LoF
namespace ICC

/--
SOURCE: ICC gist uses a distinguished free variable for `Set`.
HYPOTHESIS: the additive lane uses `var 0` as a lightweight placeholder token
because the local first-order syntax has `Nat` indices only.
-/
def Set : Term :=
  .var 0

/-- SOURCE: public ICC gist `Any = (Val λx(x))`. -/
def Any : Term :=
  .bridge (.var 0)

/-- SOURCE: public ICC gist `Arr`. -/
def Arr (A B : Term) : Term :=
  .bridge (.lam (.ann (.app (.var 1) (.ann (.var 0) (A.shift 1))) (B.shift 1)))

/-- SOURCE: public ICC gist `All`. -/
def All (A B : Term) : Term :=
  .bridge (.lam (.ann (.app (.var 1) (.ann (.var 0) (A.shift 1))) (.app (B.shift 1) (.var 0))))

/-- SOURCE: public ICC gist `Ind`. -/
def Ind (A B : Term) : Term :=
  .bridge (.lam (.ann (.app (.var 1) (.ann (.var 0) (A.shift 1))) (.app (.app (B.shift 2) (.var 1)) (.var 0))))

/--
HYPOTHESIS: placeholder Σ-like shell for the additive lane.

The public user proposal mentions `Sig`, but the current local ICC lane has no
pair or projection syntax. This definition is intentionally weak and is not
claimed as a faithful dependent-pair implementation.
-/
def Sig (A B : Term) : Term :=
  .bridge (.ann (.var 0) (.app (B.shift 1) (.ann (.var 0) (A.shift 1))))

end ICC
end LoF
end HeytingLean
