import HeytingLean.InqBQ.Imported.H10UPCPatch31BridgeTest

namespace HeytingLean
namespace InqBQ

open Nat.Partrec

def importedH10UPCEquiv : TranslationKernelV2.h10upc ≃ H10UPC :=
  Equiv.refl _

instance instPrimcodableImportedH10UPC : Primcodable TranslationKernelV2.h10upc :=
  Primcodable.ofEquiv H10UPC importedH10UPCEquiv

theorem importedDecidable_of_computablePred
    {α : Type*} [Primcodable α] {p : α → Prop}
    (hp : ComputablePred p) :
    TranslationKernelV2.decidable α p := by
  rcases ComputablePred.computable_iff.1 hp with ⟨b, _, hpEq⟩
  exact
    TranslationKernelV2.ex.ex_intro
      (α → Bool)
      (fun f => ∀ x : α, p x ↔ f x = Bool.true)
      b
      (by
        intro x
        simpa [hpEq])

theorem imported_h10upcSat_compl_iff_local (cs : List H10UPC) :
    TranslationKernelV2.complement
        (List H10UPC)
        TranslationKernelV2.H10UPC_SAT cs ↔
      ¬ H10UPCSat cs := by
  simpa [TranslationKernelV2.complement] using
    not_congr (HeytingLean.InqBQ.Imported.imported_h10upc_sat_iff_local cs)

theorem imported_h10upcSat_compl_not_computable :
    ¬ ComputablePred (fun cs : List H10UPC => ¬ H10UPCSat cs) := by
  intro hcomp
  have hImported :
      ComputablePred
        (fun cs : List H10UPC =>
          TranslationKernelV2.complement
            (List H10UPC)
            TranslationKernelV2.H10UPC_SAT cs) :=
    ComputablePred.of_eq hcomp (fun cs => (imported_h10upcSat_compl_iff_local cs).symm)
  exact TranslationKernelV2.H10UPC_SAT_compl_undec
    (importedDecidable_of_computablePred hImported)

theorem imported_h10upcSat_compl_not_re :
    ¬ REPred (fun cs : List H10UPC => ¬ H10UPCSat cs) :=
  h10upcSat_compl_not_re_of_not_computable
    imported_h10upcSat_compl_not_computable

end InqBQ
end HeytingLean
