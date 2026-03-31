import HeytingLean.Noneism.Syntax.Henkin

namespace HeytingLean
namespace Noneism
namespace Syntax
namespace Henkin

@[simp] theorem liftTerm_substTerm_var' {κ : Type} (x a : Var) (t : Term) :
    liftTerm (κ := κ) (Syntax.substTerm x (.var a) t) =
      substTerm x (.var a) (liftTerm (κ := κ) t) := by
  exact liftTerm_substTerm_var (κ := κ) x a t

@[simp] theorem liftFormula_substFormula_var {σ κ : Type} (x a : Var) :
    (φ : Formula σ) ->
      liftFormula (σ := σ) (κ := κ) (Syntax.substFormula (σ := σ) x (.var a) φ) =
      substFormula x (.var a) (liftFormula (σ := σ) (κ := κ) φ)
  | .top => by
      simp [Syntax.substFormula, substFormula, liftFormula]
  | .bot => by
      simp [Syntax.substFormula, substFormula, liftFormula]
  | .pred p args => by
      simp [Syntax.substFormula, substFormula, Syntax.substTerms, substTerms, liftFormula,
        List.map_map, Function.comp]
  | .eExists t => by
      simp [Syntax.substFormula, substFormula, liftFormula]
  | .not φ => by
      simp [Syntax.substFormula, substFormula, liftFormula,
        liftFormula_substFormula_var (σ := σ) (κ := κ) x a φ]
  | .and φ ψ => by
      simp [Syntax.substFormula, substFormula, liftFormula,
        liftFormula_substFormula_var (σ := σ) (κ := κ) x a φ,
        liftFormula_substFormula_var (σ := σ) (κ := κ) x a ψ]
  | .or φ ψ => by
      simp [Syntax.substFormula, substFormula, liftFormula,
        liftFormula_substFormula_var (σ := σ) (κ := κ) x a φ,
        liftFormula_substFormula_var (σ := σ) (κ := κ) x a ψ]
  | .imp φ ψ => by
      simp [Syntax.substFormula, substFormula, liftFormula,
        liftFormula_substFormula_var (σ := σ) (κ := κ) x a φ,
        liftFormula_substFormula_var (σ := σ) (κ := κ) x a ψ]
  | .sigma z φ => by
      by_cases hzx : z = x
      · simp [Syntax.substFormula, substFormula, liftFormula, hzx]
      · by_cases hza : z = a
        · subst hza
          by_cases hxfv : x ∈ Syntax.fvFormula (σ := σ) φ
          · have hzmemS : z ∈ Syntax.fvTerm (.var z) := by simp [Syntax.fvTerm]
            have hzmemH : z ∈ fvTerm (.var z : TermH κ) := by simp [fvTerm]
            have hxfvH : x ∈ fvFormula (liftFormula (σ := σ) (κ := κ) φ) := by
              simpa [fvFormula_liftFormula, Syntax.fvFormula] using hxfv
            let avoid : Finset Var :=
              Syntax.varsFormula (σ := σ) φ ∪ Syntax.fvTerm (.var z) ∪ ({x, z} : Finset Var)
            let z' : Var := freshVar avoid
            have hrec :
                liftFormula (σ := σ) (κ := κ)
                    (Syntax.substFormula (σ := σ) x (.var z)
                      (Syntax.renameFormula (σ := σ) z z' φ)) =
                  substFormula x (.var z)
                    (liftFormula (σ := σ) (κ := κ)
                      (Syntax.renameFormula (σ := σ) z z' φ)) :=
              liftFormula_substFormula_var (σ := σ) (κ := κ) x z
                (Syntax.renameFormula (σ := σ) z z' φ)
            have hbody :
                liftFormula (σ := σ) (κ := κ)
                    (Syntax.substFormula (σ := σ) x (.var z)
                      (Syntax.renameFormula (σ := σ) z z' φ)) =
                  substFormula x (.var z)
                    (renameFormula z z' (liftFormula (σ := σ) (κ := κ) φ)) := by
              simpa [liftFormula_renameFormula] using hrec
            have hsigma :
                FormulaH.sigma z'
                    (liftFormula (σ := σ) (κ := κ)
                      (Syntax.substFormula (σ := σ) x (.var z)
                        (Syntax.renameFormula (σ := σ) z z' φ))) =
                  FormulaH.sigma z'
                    (substFormula x (.var z)
                      (renameFormula z z' (liftFormula (σ := σ) (κ := κ) φ))) :=
              congrArg (FormulaH.sigma z') hbody
            simpa [avoid, z', Syntax.substFormula, substFormula, liftFormula,
              hzx, hzmemS, hzmemH, hxfv, hxfvH, varsFormula_liftFormula, Syntax.varsFormula,
              Syntax.fvTerm, fvTerm] using hsigma
          · simp [Syntax.substFormula, substFormula, liftFormula, hzx, hxfv,
              liftFormula_substFormula_var (σ := σ) (κ := κ) x z φ]
        · have hz_not_memS : z ∉ Syntax.fvTerm (.var a) := by
            simp [Syntax.fvTerm, hza]
          have hz_not_memH : z ∉ fvTerm (.var a : TermH κ) := by
            simp [fvTerm, hza]
          have hcapS : ¬(z ∈ Syntax.fvTerm (.var a) ∧ x ∈ Syntax.fvFormula (σ := σ) φ) := by
            intro h
            exact hz_not_memS h.1
          have hcapH : ¬(z ∈ fvTerm (.var a : TermH κ) ∧ x ∈ fvFormula (liftFormula (σ := σ) (κ := κ) φ)) := by
            intro h
            exact hz_not_memH h.1
          simp [Syntax.substFormula, substFormula, liftFormula, hzx, hz_not_memS, hz_not_memH,
            liftFormula_substFormula_var (σ := σ) (κ := κ) x a φ]
  | .pi z φ => by
      by_cases hzx : z = x
      · simp [Syntax.substFormula, substFormula, liftFormula, hzx]
      · by_cases hza : z = a
        · subst hza
          by_cases hxfv : x ∈ Syntax.fvFormula (σ := σ) φ
          · have hzmemS : z ∈ Syntax.fvTerm (.var z) := by simp [Syntax.fvTerm]
            have hzmemH : z ∈ fvTerm (.var z : TermH κ) := by simp [fvTerm]
            have hxfvH : x ∈ fvFormula (liftFormula (σ := σ) (κ := κ) φ) := by
              simpa [fvFormula_liftFormula, Syntax.fvFormula] using hxfv
            let avoid : Finset Var :=
              Syntax.varsFormula (σ := σ) φ ∪ Syntax.fvTerm (.var z) ∪ ({x, z} : Finset Var)
            let z' : Var := freshVar avoid
            have hrec :
                liftFormula (σ := σ) (κ := κ)
                    (Syntax.substFormula (σ := σ) x (.var z)
                      (Syntax.renameFormula (σ := σ) z z' φ)) =
                  substFormula x (.var z)
                    (liftFormula (σ := σ) (κ := κ)
                      (Syntax.renameFormula (σ := σ) z z' φ)) :=
              liftFormula_substFormula_var (σ := σ) (κ := κ) x z
                (Syntax.renameFormula (σ := σ) z z' φ)
            have hbody :
                liftFormula (σ := σ) (κ := κ)
                    (Syntax.substFormula (σ := σ) x (.var z)
                      (Syntax.renameFormula (σ := σ) z z' φ)) =
                  substFormula x (.var z)
                    (renameFormula z z' (liftFormula (σ := σ) (κ := κ) φ)) := by
              simpa [liftFormula_renameFormula] using hrec
            have hpi :
                FormulaH.pi z'
                    (liftFormula (σ := σ) (κ := κ)
                      (Syntax.substFormula (σ := σ) x (.var z)
                        (Syntax.renameFormula (σ := σ) z z' φ))) =
                  FormulaH.pi z'
                    (substFormula x (.var z)
                      (renameFormula z z' (liftFormula (σ := σ) (κ := κ) φ))) :=
              congrArg (FormulaH.pi z') hbody
            simpa [avoid, z', Syntax.substFormula, substFormula, liftFormula,
              hzx, hzmemS, hzmemH, hxfv, hxfvH, varsFormula_liftFormula, Syntax.varsFormula,
              Syntax.fvTerm, fvTerm] using hpi
          · simp [Syntax.substFormula, substFormula, liftFormula, hzx, hxfv,
              liftFormula_substFormula_var (σ := σ) (κ := κ) x z φ]
        · have hz_not_memS : z ∉ Syntax.fvTerm (.var a) := by
            simp [Syntax.fvTerm, hza]
          have hz_not_memH : z ∉ fvTerm (.var a : TermH κ) := by
            simp [fvTerm, hza]
          have hcapS : ¬(z ∈ Syntax.fvTerm (.var a) ∧ x ∈ Syntax.fvFormula (σ := σ) φ) := by
            intro h
            exact hz_not_memS h.1
          have hcapH : ¬(z ∈ fvTerm (.var a : TermH κ) ∧ x ∈ fvFormula (liftFormula (σ := σ) (κ := κ) φ)) := by
            intro h
            exact hz_not_memH h.1
          simp [Syntax.substFormula, substFormula, liftFormula, hzx, hz_not_memS, hz_not_memH,
            liftFormula_substFormula_var (σ := σ) (κ := κ) x a φ]
termination_by
  φ => Syntax.fSize (σ := σ) φ
decreasing_by
  all_goals
    simp [Syntax.fSize, Syntax.fSize_renameFormula]
    try omega

end Henkin
end Syntax
end Noneism
end HeytingLean
