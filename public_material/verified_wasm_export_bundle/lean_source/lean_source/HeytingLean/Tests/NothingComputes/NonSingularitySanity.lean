import HeytingLean.Noneism.NothingComputes.NonSingularity

namespace HeytingLean.Tests.NothingComputes

open HeytingLean.Numbers.Surreal.NoneistKripke

def varyingWorld : World := { stage := 1, mode := .possible }

example : ¬ HeytingLean.Noneism.NothingComputes.SingularNothingAt .constant varyingWorld := by
  exact HeytingLean.Noneism.NothingComputes.nothing_not_singular_constant varyingWorld

example : ¬ HeytingLean.Noneism.NothingComputes.SingularNothingAt .varying varyingWorld := by
  exact HeytingLean.Noneism.NothingComputes.nothing_not_singular_exact varyingWorld (by simp [varyingWorld])

end HeytingLean.Tests.NothingComputes
