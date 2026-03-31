import HeytingLean.Certified.Program
import HeytingLean.Certified.Properties

namespace HeytingLean
namespace Certified

namespace CertifiedLibrary

private def idParts (id : ProgramId) : List String :=
  (id.splitOn "∘").filter (· ≠ "")

private def composeCStub (f g : CertifiedProgram) : String :=
  let parts := idParts f.id ++ idParts g.id
  let name := String.intercalate " ∘ " parts
  s!"/* composed: {name} */\n"

private theorem holds_precompStable
    (p : Property) {A B C : Ty} (f : B.interp → C.interp) (g : A.interp → B.interp) :
    Property.precompStable p = true →
    Property.Holds p B C f →
    Property.Holds p A C (fun a => f (g a)) := by
  cases p with
  | boundedNat lo hi =>
      cases C with
      | nat =>
          intro _ hf a
          simpa using hf (g a)
      | int =>
          intro _ hf
          exact False.elim hf
      | listNat =>
          intro _ hf
          exact False.elim hf
      | u32 =>
          intro _ hf
          exact False.elim hf
      | prod _ _ =>
          intro _ hf
          exact False.elim hf
  | monotone =>
      intro h
      cases h
  | conservative =>
      intro h
      cases h
  | nonnegInt =>
      cases C with
      | nat =>
          intro _ hf
          exact False.elim hf
      | int =>
          intro _ hf a
          simpa using hf (g a)
      | listNat =>
          intro _ hf
          exact False.elim hf
      | u32 =>
          intro _ hf
          exact False.elim hf
      | prod _ _ =>
          intro _ hf
          exact False.elim hf
  | custom name =>
      intro _ _
      trivial

private theorem holds_monotone_comp
    {A B C : Ty} (f : B.interp → C.interp) (g : A.interp → B.interp) :
    Property.Holds .monotone B C f →
    Property.Holds .monotone A B g →
    Property.Holds .monotone A C (fun a => f (g a)) := by
  cases A <;> cases B <;> cases C <;>
    simp [Property.Holds] <;> intro hf hg <;> exact hf.comp hg

private theorem holds_conservative_comp
    {A B C : Ty} (f : B.interp → C.interp) (g : A.interp → B.interp) :
    Property.Holds .conservative B C f →
    Property.Holds .conservative A B g →
    Property.Holds .conservative A C (fun a => f (g a)) := by
  cases A <;> cases B <;> cases C <;>
    simp [Property.Holds] <;> intro hf hg <;> intro x <;> simp [hf, hg]

/-- Compose two certified programs (if the types match) and propagate properties conservatively. -/
def composePrograms? (f g : CertifiedProgram) : Option CertifiedProgram := do
  match f with
  | { id := _, name := _, version := fVersion
      dom := fDom, cod := fCod
      dimension := fDim, lenses := fLenses
      properties := fProps, invariants := fInvs
      fn := fFn, propProofs := fPropProofs
      cCode := _, cHash := _, cHashOk := _ } =>
    match g with
    | { id := _, name := _, version := _
        dom := gDom, cod := gCod
        dimension := _, lenses := _
        properties := gProps, invariants := _
        fn := gFn, propProofs := gPropProofs
        cCode := _, cHash := _, cHashOk := _ } =>
      if h : fDom = gCod then
        match h with
        | rfl =>
            let dom := gDom
            let cod := fCod
            let fn : dom.interp → cod.interp := fun x => fFn (gFn x)
            let stable : List Property := fProps.filter Property.precompStable
            let monCond : Prop := Property.monotone ∈ fProps ∧ Property.monotone ∈ gProps
            let monProps : List Property := if monCond then [Property.monotone] else []
            let consCond : Prop := Property.conservative ∈ fProps ∧ Property.conservative ∈ gProps
            let consProps : List Property := if consCond then [Property.conservative] else []
            let derived : List Property := (stable ++ monProps) ++ consProps
            let cCode := composeCStub f g
            let id := s!"{f.id}∘{g.id}"
            some <|
              CertifiedProgram.mkHashed
                (id := id)
                (name := id)
                (version := fVersion)
                (dom := dom) (cod := cod)
                (dimension := fDim)
                (lenses := fLenses)
                (properties := derived)
                (invariants := fInvs)
                (fn := fn)
                (propProofs := by
              intro p hp
              have hp₁ : p ∈ stable ++ monProps ∨ p ∈ consProps := by
                simpa [derived] using (List.mem_append.mp hp)
              cases p with
              | boundedNat lo hi =>
                  have hs : Property.boundedNat lo hi ∈ stable := by
                    cases hp₁ with
                    | inl h =>
                        have h' :
                            Property.boundedNat lo hi ∈ stable ∨
                              Property.boundedNat lo hi ∈ monProps := by
                          simpa using (List.mem_append.mp h)
                        cases h' with
                        | inl hs => exact hs
                        | inr hm =>
                            by_cases hMon : monCond
                            ·
                                have : False := by
                                  simp [monProps, hMon] at hm
                                exact False.elim this
                            ·
                                have : False := by
                                  simp [monProps, hMon] at hm
                                exact False.elim this
                    | inr h =>
                        by_cases hCons : consCond
                        ·
                            have : False := by
                              simp [consProps, hCons] at h
                            exact False.elim this
                        ·
                            have : False := by
                              simp [consProps, hCons] at h
                            exact False.elim this
                  have hpF : Property.boundedNat lo hi ∈ fProps := (List.mem_filter.mp hs).1
                  have hf : Property.Holds (.boundedNat lo hi) fDom fCod fFn :=
                    fPropProofs (.boundedNat lo hi) hpF
                  have hStable : Property.precompStable (.boundedNat lo hi) = true :=
                    (List.mem_filter.mp hs).2
                  exact holds_precompStable (p := .boundedNat lo hi) (f := fFn) (g := gFn) hStable hf
              | monotone =>
                  by_cases hMon : monCond
                  · have hf : Property.Holds .monotone fDom fCod fFn :=
                      fPropProofs .monotone hMon.1
                    have hg : Property.Holds .monotone gDom fDom gFn :=
                      gPropProofs .monotone hMon.2
                    exact holds_monotone_comp (f := fFn) (g := gFn) hf hg
                  · have : False := by
                      cases hp₁ with
                      | inl h =>
                          have h' : Property.monotone ∈ stable ∨ Property.monotone ∈ monProps := by
                            simpa using (List.mem_append.mp h)
                          cases h' with
                          | inl hs =>
                              have hPred : Property.precompStable Property.monotone = true :=
                                (List.mem_filter.mp hs).2
                              simp [Property.precompStable] at hPred
                          | inr hm =>
                              simp [monProps, hMon] at hm
                      | inr h =>
                          by_cases hCons : consCond
                          · have : False := by
                              simp [consProps, hCons] at h
                            exact this
                          · have : False := by
                              simp [consProps, hCons] at h
                            exact this
                    exact False.elim this
              | conservative =>
                  by_cases hCons : consCond
                  · have hf : Property.Holds .conservative fDom fCod fFn :=
                      fPropProofs .conservative hCons.1
                    have hg : Property.Holds .conservative gDom fDom gFn :=
                      gPropProofs .conservative hCons.2
                    exact holds_conservative_comp (f := fFn) (g := gFn) hf hg
                  · have : False := by
                      cases hp₁ with
                      | inl h =>
                          have h' : Property.conservative ∈ stable ∨ Property.conservative ∈ monProps := by
                            simpa using (List.mem_append.mp h)
                          cases h' with
                          | inl hs =>
                              have hPred : Property.precompStable Property.conservative = true :=
                                (List.mem_filter.mp hs).2
                              simp [Property.precompStable] at hPred
                          | inr hm =>
                              by_cases hMon : monCond
                              · have : False := by
                                  simp [monProps, hMon] at hm
                                exact this
                              · have : False := by
                                  simp [monProps, hMon] at hm
                                exact this
                      | inr h =>
                          have : False := by
                            simp [consProps, hCons] at h
                          exact this
                    exact False.elim this
              | nonnegInt =>
                  have hs : Property.nonnegInt ∈ stable := by
                    cases hp₁ with
                    | inl h =>
                        have h' : Property.nonnegInt ∈ stable ∨ Property.nonnegInt ∈ monProps := by
                          simpa using (List.mem_append.mp h)
                        cases h' with
                        | inl hs => exact hs
                        | inr hm =>
                            by_cases hMon : monCond
                            ·
                                have : False := by
                                  simp [monProps, hMon] at hm
                                exact False.elim this
                            ·
                                have : False := by
                                  simp [monProps, hMon] at hm
                                exact False.elim this
                    | inr h =>
                        by_cases hCons : consCond
                        ·
                            have : False := by
                              simp [consProps, hCons] at h
                            exact False.elim this
                        ·
                            have : False := by
                              simp [consProps, hCons] at h
                            exact False.elim this
                  have hpF : Property.nonnegInt ∈ fProps := (List.mem_filter.mp hs).1
                  have hf : Property.Holds .nonnegInt fDom fCod fFn := fPropProofs .nonnegInt hpF
                  have hStable : Property.precompStable .nonnegInt = true := (List.mem_filter.mp hs).2
                  exact holds_precompStable (p := .nonnegInt) (f := fFn) (g := gFn) hStable hf
              | custom name =>
                  have hs : Property.custom name ∈ stable := by
                    cases hp₁ with
                    | inl h =>
                        have h' : Property.custom name ∈ stable ∨ Property.custom name ∈ monProps := by
                          simpa using (List.mem_append.mp h)
                        cases h' with
                        | inl hs => exact hs
                        | inr hm =>
                            by_cases hMon : monCond
                            ·
                                have : False := by
                                  simp [monProps, hMon] at hm
                                exact False.elim this
                            ·
                                have : False := by
                                  simp [monProps, hMon] at hm
                                exact False.elim this
                    | inr h =>
                        by_cases hCons : consCond
                        ·
                            have : False := by
                              simp [consProps, hCons] at h
                            exact False.elim this
                        ·
                            have : False := by
                              simp [consProps, hCons] at h
                            exact False.elim this
                  have hpF : Property.custom name ∈ fProps := (List.mem_filter.mp hs).1
                  have hf : Property.Holds (.custom name) fDom fCod fFn :=
                    fPropProofs (.custom name) hpF
                  have hStable : Property.precompStable (.custom name) = true := (List.mem_filter.mp hs).2
                  exact holds_precompStable (p := .custom name) (f := fFn) (g := gFn) hStable hf)
                (cCode := cCode)
      else
        none

end CertifiedLibrary

end Certified
end HeytingLean
