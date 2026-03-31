import HeytingLean.Noneism.Semantics.LP

namespace HeytingLean
namespace Noneism
namespace Tests

open LP

/-- LP: `A ∧ ¬A` can be designated while `B` is not (non-triviality witness). -/
theorem lp_non_triviality :
    LP.TV.designated (LP.eval LP.counterEnv (.and LP.A (.not LP.A))) ∧
    ¬ LP.TV.designated (LP.eval LP.counterEnv LP.B) := by
  exact And.intro LP.contradiction_designated LP.b_not_designated

/-- LP entailment: explosion (ECQ) fails at the entailment level. -/
theorem lp_no_ECQ :
    ¬ LP.Entails [LP.A, .not LP.A] LP.B := by
  -- Witness environment where premises are designated but B is not.
  intro h
  have hPrem : (∀ ψ ∈ [LP.A, .not LP.A], LP.Holds LP.counterEnv ψ) := by
    intro ψ hmem
    have : ψ = LP.A ∨ ψ = .not LP.A := by
      simpa using List.mem_cons.mp hmem
    rcases this with hA | hNotA
    · subst hA; simpa [LP.Holds] using LP.contradiction_designated
    · subst hNotA
      -- Show ¬A is designated under the counter environment
      have : LP.TV.designated (LP.eval LP.counterEnv (.not LP.A)) := by
        -- From `A` both, `¬A` both
        simp [LP.eval, LP.A, LP.TV.designated, LP.TV.not, LP.counterEnv]
      simpa [LP.Holds] using this
  have hB : LP.Holds LP.counterEnv LP.B := h LP.counterEnv hPrem
  -- But B is not designated under the counter environment.
  have : ¬ LP.Holds LP.counterEnv LP.B := by
    simpa [LP.Holds] using LP.b_not_designated
  exact this hB

end Tests
end Noneism
end HeytingLean
