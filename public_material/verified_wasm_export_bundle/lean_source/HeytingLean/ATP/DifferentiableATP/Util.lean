/-!
# ATP.DifferentiableATP.Util

Small shared helpers for the differentiable ATP extension.
-/

namespace HeytingLean
namespace ATP
namespace DifferentiableATP

def absRat (r : Rat) : Rat :=
  if r < 0 then -r else r

end DifferentiableATP
end ATP
end HeytingLean
