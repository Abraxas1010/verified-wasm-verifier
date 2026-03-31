import HeytingLean.LoF.ICC.Reduction

namespace HeytingLean
namespace LoF
namespace ICC

/--
`YFree` is the current sprint's honest fragment boundary:
the existing executable `isYFree` checker from `Reduction.lean`, re-exposed as a proposition.

This is intentionally modest. It does not claim unrestricted-`Y` soundness; it fixes
the fragment boundary on the exact syntax and checker the additive ICC lane already ships.
-/
def YFree (t : Term) : Prop :=
  isYFree t = true

@[simp] theorem containsLegacyYShim_kTerm :
    containsLegacyYShim kTerm = false := by
  native_decide

@[simp] theorem containsLegacyYShim_sTerm :
    containsLegacyYShim sTerm = false := by
  native_decide

@[simp] theorem containsLegacyYShim_legacyY :
    containsLegacyYShim legacyY = true := by
  native_decide

@[simp] theorem containsLegacyYShim_embedLegacy (t : LoF.Comb) :
    containsLegacyYShim (embedLegacy t) = legacyContainsY t := by
  induction t with
  | K =>
      simp [embedLegacy, legacyContainsY]
  | S =>
      simp [embedLegacy, legacyContainsY]
  | Y =>
      simp [embedLegacy, legacyContainsY]
  | app fn arg ihFn ihArg =>
      simp [embedLegacy, legacyContainsY, ihFn, ihArg, containsLegacyYShim]

@[simp] theorem yFree_legacyY : ¬ YFree legacyY := by
  simp [YFree, isYFree, containsLegacyYShim, legacyY]

@[simp] theorem yFree_embedLegacy_iff (t : LoF.Comb) :
    YFree (embedLegacy t) ↔ legacyContainsY t = false := by
  simp [YFree, isYFree]

theorem checkYFree_sound {fuel : Nat} {t : Term}
    (h : checkYFree fuel t = true) :
    YFree t ∧ step? (reduceFuel fuel t) = none := by
  rw [checkYFree, Bool.and_eq_true] at h
  constructor
  · exact h.1
  · cases hstep : step? (reduceFuel fuel t) <;> simp [hstep] at h
    simp

end ICC
end LoF
end HeytingLean
