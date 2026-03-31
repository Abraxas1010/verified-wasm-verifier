import HeytingLean.Noneism.Contextuality.Basic

namespace HeytingLean
namespace Noneism
namespace Contextuality

abbrev Witness {M : Type u} {O : Type v} [Fintype M] [DecidableEq M]
    (S : Scenario M O) := {C // C ∈ S.cover}

abbrev Actualize {M : Type u} {O : Type v} [Fintype M] [DecidableEq M]
    (S : Scenario M O) (w : Witness S) :=
  {s : LocalAssign w.1 O // S.Allowed w.1 s}

theorem isGlobalSection_iff_witness_actualization {M : Type u} {O : Type v}
    [Fintype M] [DecidableEq M] (S : Scenario M O) (g : M → O) :
    IsGlobalSection S g ↔ ∀ w : Witness S, S.Allowed w.1 (restrict g w.1) := by
  constructor
  · intro h w
    exact h w.1 w.2
  · intro h C hC
    exact h ⟨C, hC⟩

theorem no_universal_actualization {M : Type u} {O : Type v}
    [Fintype M] [DecidableEq M] (S : Scenario M O) :
    Contextual S → ¬ ∃ g : M → O, ∀ w : Witness S, S.Allowed w.1 (restrict g w.1) := by
  intro hctx h
  apply hctx
  rcases h with ⟨g, hg⟩
  exact ⟨g, (isGlobalSection_iff_witness_actualization S g).2 hg⟩

theorem contextual_iff_no_universal_actualization {M : Type u} {O : Type v}
    [Fintype M] [DecidableEq M] (S : Scenario M O) :
    Contextual S ↔ ¬ ∃ g : M → O, ∀ w : Witness S, S.Allowed w.1 (restrict g w.1) := by
  constructor
  · exact no_universal_actualization S
  · intro h hGlobal
    apply h
    rcases hGlobal with ⟨g, hg⟩
    exact ⟨g, (isGlobalSection_iff_witness_actualization S g).1 hg⟩

end Contextuality
end Noneism
end HeytingLean
