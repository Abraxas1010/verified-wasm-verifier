import HeytingLean.Hyperseries.Transmonomials

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Hyperseries

example : Transmonomial.height Transmonomial.one = 0 := by
  simp

example : Transmonomial.height (Transmonomial.omegaPow 3) = 1 := by
  simp

example :
    Transmonomial.height
        (Transmonomial.exp (Transmonomial.log (Transmonomial.omegaPow 2))) = 3 := by
  simp

example (e : BaseExponent) : Transmonomial.ofBaseExponent e = Transmonomial.omegaPow e := by
  rfl

example :
    Transmonomial.iterExp 3 (Transmonomial.omegaPow 2) =
      Transmonomial.exp (Transmonomial.exp (Transmonomial.exp (Transmonomial.omegaPow 2))) := by
  rfl

example :
    Transmonomial.iterLog 2 (Transmonomial.exp (Transmonomial.omegaPow 4)) =
      Transmonomial.log (Transmonomial.log (Transmonomial.exp (Transmonomial.omegaPow 4))) := by
  rfl

example :
    Transmonomial.height (Transmonomial.iterExp 4 (Transmonomial.omegaPow 0)) = 5 := by
  exact Transmonomial.height_iterExp 4 (Transmonomial.omegaPow 0)

example :
    Transmonomial.height (Transmonomial.iterLog 3 Transmonomial.one) = 3 := by
  exact Transmonomial.height_iterLog 3 Transmonomial.one

end Numbers
end Tests
end HeytingLean
