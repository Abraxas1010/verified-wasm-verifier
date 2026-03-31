import HeytingLean.InqBQ.H10UPCComputability
import HeytingLean.InqBQ.Imported.H10UPCPatch31Local

open HeytingLean.InqBQ
open TranslationKernelV2

namespace HeytingLean.InqBQ.Imported

lemma in_iff_mem {α : Type} (x : α) : ∀ xs : List α, TranslationKernelV2.In α x xs ↔ x ∈ xs
  | [] => by simp [TranslationKernelV2.In]
  | y :: ys => by
      simp [TranslationKernelV2.In, in_iff_mem (x := x) ys, eq_comm]

lemma ex_iff_exists {α : Type} {P : α → Prop} : TranslationKernelV2.ex α P ↔ ∃ x, P x := by
  constructor
  · intro h
    cases h with
    | intro x hx => exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact TranslationKernelV2.ex.intro x hx

lemma imported_h10upc_sat_iff_local (cs : List TranslationKernelV2.h10upc) :
    TranslationKernelV2.H10UPC_SAT cs ↔ HeytingLean.InqBQ.H10UPCSat cs := by
  constructor
  · intro h
    rcases (ex_iff_exists.mp h) with ⟨ρ, hρ⟩
    refine ⟨ρ, ?_⟩
    intro c hc
    exact hρ c ((in_iff_mem c cs).2 hc)
  · rintro ⟨ρ, hρ⟩
    refine (ex_iff_exists).2 ?_
    refine ⟨ρ, ?_⟩
    intro c hc
    exact hρ c ((in_iff_mem c cs).1 hc)

end HeytingLean.InqBQ.Imported
