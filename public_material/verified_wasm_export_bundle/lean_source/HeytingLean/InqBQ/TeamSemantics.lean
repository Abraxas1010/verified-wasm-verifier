import HeytingLean.InqBQ.Finiteness

namespace HeytingLean
namespace InqBQ

open Set

/-- Teams as sets of assignments. -/
abbrev Team (D : Type) := Set (Assignment D)

variable {M : InfoModel SigmaAB}

/-- The team induced by a state, tracking the `a` and `b` values in variables `0` and `1`. -/
def inducedTeam (M : InfoModel SigmaAB) (s : Set M.W) (g : Assignment M.D) : Team M.D :=
  { g' | ∃ w ∈ s,
      g' = (Assignment.update (Assignment.update g 0 (M.nonrigidInterp w ABConst.a SigmaAB.noArgs))
              1 (M.nonrigidInterp w ABConst.b SigmaAB.noArgs)) }

/-- Team-semantic functional dependence of variable `1` on variable `0`. -/
def teamDepends (T : Team M.D) : Prop :=
  ∀ ⦃g₁ g₂ : Assignment M.D⦄, g₁ ∈ T → g₂ ∈ T → g₁ 0 = g₂ 0 → g₁ 1 = g₂ 1

theorem teamDepends_iff_function (s : Set M.W) (g : Assignment M.D) :
    teamDepends (M := M) (inducedTeam M s g) ↔
      RelIsFunction (associatedRelation M s) := by
  constructor
  · intro hTeam d e₁ e₂ h1 h2
    rcases h1 with ⟨w1, hw1, hw1pair⟩
    rcases h2 with ⟨w2, hw2, hw2pair⟩
    have hg1 :
        (Assignment.update (Assignment.update g 0 (M.nonrigidInterp w1 ABConst.a SigmaAB.noArgs))
          1 (M.nonrigidInterp w1 ABConst.b SigmaAB.noArgs)) ∈ inducedTeam M s g := by
      exact ⟨w1, hw1, rfl⟩
    have hg2 :
        (Assignment.update (Assignment.update g 0 (M.nonrigidInterp w2 ABConst.a SigmaAB.noArgs))
          1 (M.nonrigidInterp w2 ABConst.b SigmaAB.noArgs)) ∈ inducedTeam M s g := by
      exact ⟨w2, hw2, rfl⟩
    have h0 :
        (Assignment.update (Assignment.update g 0 (M.nonrigidInterp w1 ABConst.a SigmaAB.noArgs))
          1 (M.nonrigidInterp w1 ABConst.b SigmaAB.noArgs)) 0 =
        (Assignment.update (Assignment.update g 0 (M.nonrigidInterp w2 ABConst.a SigmaAB.noArgs))
          1 (M.nonrigidInterp w2 ABConst.b SigmaAB.noArgs)) 0 := by
      simpa [Assignment.update, associatedPair] using
        (congrArg Prod.fst hw1pair).trans (congrArg Prod.fst hw2pair).symm
    have h1eq := hTeam hg1 hg2 h0
    have hb :
        M.nonrigidInterp w1 ABConst.b SigmaAB.noArgs =
        M.nonrigidInterp w2 ABConst.b SigmaAB.noArgs := by
      simpa [Assignment.update] using h1eq
    calc
      e₁ = M.nonrigidInterp w1 ABConst.b SigmaAB.noArgs := by
        simpa [associatedPair] using (congrArg Prod.snd hw1pair).symm
      _ = M.nonrigidInterp w2 ABConst.b SigmaAB.noArgs := hb
      _ = e₂ := by
        simpa [associatedPair] using congrArg Prod.snd hw2pair
  · intro hFun g₁ g₂ hg₁ hg₂ h0
    rcases hg₁ with ⟨w1, hw1, rfl⟩
    rcases hg₂ with ⟨w2, hw2, rfl⟩
    have hw1rel :
        (M.nonrigidInterp w1 ABConst.a SigmaAB.noArgs,
          M.nonrigidInterp w1 ABConst.b SigmaAB.noArgs) ∈ associatedRelation M s := by
      exact ⟨w1, hw1, rfl⟩
    have hw2rel :
        (M.nonrigidInterp w2 ABConst.a SigmaAB.noArgs,
          M.nonrigidInterp w2 ABConst.b SigmaAB.noArgs) ∈ associatedRelation M s := by
      exact ⟨w2, hw2, rfl⟩
    have hfst :
        M.nonrigidInterp w1 ABConst.a SigmaAB.noArgs =
        M.nonrigidInterp w2 ABConst.a SigmaAB.noArgs := by
      simpa [Assignment.update] using h0
    have hsnd :
        M.nonrigidInterp w1 ABConst.b SigmaAB.noArgs =
        M.nonrigidInterp w2 ABConst.b SigmaAB.noArgs := by
      exact hFun (by simpa [hfst] using hw1rel) hw2rel
    simpa [Assignment.update] using hsnd

theorem dep_team_equiv
    (hid : M.isIdModel) (s : Set M.W) (g : Assignment M.D) :
    supports M s g (Formula.dependence SigmaAB.termA SigmaAB.termB) ↔
      teamDepends (M := M) (inducedTeam M s g) := by
  rw [teamDepends_iff_function, supports_dep_ab hid s g]

end InqBQ
end HeytingLean
