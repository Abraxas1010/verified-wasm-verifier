import HeytingLean.Hyperseries.TransmonomialSemantics
import HeytingLean.Hyperseries.Equivalence

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Hyperseries
open HeytingLean.Hyperseries.Transmonomial

noncomputable section

abbrev Sid : SurrealExpLogSemantics := SurrealExpLogSemantics.identity
abbrev Sneg : SurrealExpLogCore := SurrealExpLogSemantics.negCore
abbrev SnegFull : SurrealExpLogSemantics := SurrealExpLogSemantics.negSemantics
abbrev Sactive : SurrealExpLogSemantics := SurrealExpLogSemantics.active
abbrev Splaceholder : SurrealExpLogSemantics := SurrealExpLogSemantics.placeholder
abbrev SselFalse : SurrealExpLogSemantics := SurrealExpLogSemantics.select false
abbrev SselTrue : SurrealExpLogSemantics := SurrealExpLogSemantics.select true

example : HyperserialModelLaws Surreal (SurrealExpLogSemantics.toModel Sid) := by
  infer_instance

example : ¬SurrealExpLogSemantics.Nontrivial Sid := by
  simpa [Sid] using SurrealExpLogSemantics.not_nontrivial_identity

example (x : Surreal) : (SurrealExpLogSemantics.toModel Sid).exp x = x := by
  simp [Sid]

example (x : Surreal) : (SurrealExpLogSemantics.toModel Sid).log x = x := by
  simp [Sid]

example : SurrealExpLogSemantics.CoreNontrivial Sneg := by
  simpa [Sneg] using SurrealExpLogSemantics.coreNontrivial_negCore

example : SurrealExpLogSemantics.Nontrivial SnegFull := by
  simpa [SnegFull] using SurrealExpLogSemantics.nontrivial_negSemantics

example : SselFalse = SurrealExpLogSemantics.default := by
  simp [SselFalse]

example : Sactive = Splaceholder := by
  simp [Sactive, Splaceholder]

example : Sactive = SurrealExpLogSemantics.default := by
  simp [Sactive]

example : Sactive = SurrealExpLogSemantics.select false := by
  simp [Sactive]

example : SurrealExpLogSemantics.activeUseNontrivial = false := by
  simp

example : ¬SurrealExpLogSemantics.Nontrivial SurrealExpLogSemantics.active := by
  exact SurrealExpLogSemantics.not_nontrivial_active

example :
    SurrealExpLogSemantics.active ≠ SurrealExpLogSemantics.select true :=
  SurrealExpLogSemantics.active_ne_select_true

example : SselTrue = SnegFull := by
  simp [SselTrue, SnegFull]

example : ¬SurrealExpLogSemantics.Nontrivial SselFalse := by
  simpa [SselFalse] using SurrealExpLogSemantics.not_nontrivial_select_false

example : SurrealExpLogSemantics.Nontrivial SselTrue := by
  simpa [SselTrue] using SurrealExpLogSemantics.nontrivial_select_true

example : SurrealExpLogSemantics.Nontrivial (SurrealExpLogSemantics.select true) ↔ True := by
  simpa using SurrealExpLogSemantics.nontrivial_select_iff true

example : ¬SurrealExpLogSemantics.Nontrivial (SurrealExpLogSemantics.select false) ↔ True := by
  simpa using SurrealExpLogSemantics.not_nontrivial_select_iff false

example (α : Ordinal) (x : Surreal) :
    (SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select false)).hyperExp α x = x := by
  simp

example (x : Surreal) :
    (SurrealExpLogSemantics.toModel (SurrealExpLogSemantics.select true)).hyperExp 0 x = -x := by
  simp

example : HyperserialModelLaws Surreal (SurrealExpLogSemantics.toModel SnegFull) := by
  infer_instance

example (x : Surreal) : Sneg.exp x = -x := by
  rfl

example (x : Surreal) : Sneg.log x = -x := by
  rfl

example (x : Surreal) : SnegFull.exp x = -x := by
  simp [SnegFull]

example (x : Surreal) : SnegFull.log x = -x := by
  simp [SnegFull]

example (x : Surreal) : SnegFull.hyperExp 0 x = -x := by
  simp [SnegFull]

example (x : Surreal) : SnegFull.hyperLog 0 x = -x := by
  simp [SnegFull]

example [HyperserialDescription Surreal] (e : HExpr) :
    describeExpr e = describeExprWith surrealSemanticsDefault e := by
  simpa using describeExpr_eq_describeExprWith_default (e := e)

example [HyperserialDescription Surreal] (s : PilotSeries) :
    ofPilotSeries s = ofPilotSeriesWith surrealSemanticsDefault s := by
  simpa using ofPilotSeries_eq_ofPilotSeriesWith_default (s := s)

example (S : SurrealExpLogSemantics) (m : Transmonomial) :
    Transmonomial.eval (ofSurrealExpLog S) (.exp (.log m)) =
      Transmonomial.eval (ofSurrealExpLog S) m := by
  exact
    (Transmonomial.eval_exp_log
      (M := SurrealExpLogSemantics.toModel S)
      (S := ofSurrealExpLog S) m)

example (S : SurrealExpLogSemantics) (m : Transmonomial) :
    Transmonomial.eval (ofSurrealExpLog S) (.log (.exp m)) =
      Transmonomial.eval (ofSurrealExpLog S) m := by
  exact
    (Transmonomial.eval_log_exp
      (M := SurrealExpLogSemantics.toModel S)
      (S := ofSurrealExpLog S) m)

section NameWiringSmoke

#check SurrealExpLogSemantics.iterateFrom_zero
#check SurrealExpLogSemantics.iterateFrom_succ
#check SurrealExpLogSemantics.hyperExpFromCore_zero
#check SurrealExpLogSemantics.hyperExpFromCore_succ
#check SurrealExpLogSemantics.hyperLogFromCore_zero
#check SurrealExpLogSemantics.hyperLogFromCore_succ
#check SurrealExpLogSemantics.ofCore
#check SurrealExpLogSemantics.toCore
#check SurrealExpLogSemantics.select_false
#check SurrealExpLogSemantics.select_true
#check SurrealExpLogSemantics.activeUseNontrivial
#check SurrealExpLogSemantics.activeUseNontrivial_eq_false
#check SurrealExpLogSemantics.active
#check SurrealExpLogSemantics.active_eq_select
#check SurrealExpLogSemantics.active_eq_select_false
#check SurrealExpLogSemantics.active_eq_placeholder
#check SurrealExpLogSemantics.active_eq_default
#check SurrealExpLogSemantics.nontrivial_active_iff
#check SurrealExpLogSemantics.not_nontrivial_active_iff
#check SurrealExpLogSemantics.not_nontrivial_active
#check SurrealExpLogSemantics.active_ne_select_true
#check SurrealExpLogSemantics.placeholder
#check SurrealExpLogSemantics.placeholder_eq_default
#check SurrealExpLogSemantics.negSemantics_exp
#check SurrealExpLogSemantics.negSemantics_log
#check SurrealExpLogSemantics.negSemantics_hyperExp_zero
#check SurrealExpLogSemantics.negSemantics_hyperLog_zero
#check SurrealExpLogSemantics.negSemantics_hyperExp_succ
#check SurrealExpLogSemantics.negSemantics_hyperLog_succ
#check SurrealExpLogSemantics.select_false_exp
#check SurrealExpLogSemantics.select_false_log
#check SurrealExpLogSemantics.select_false_hyperExp
#check SurrealExpLogSemantics.select_false_hyperLog
#check SurrealExpLogSemantics.select_true_exp
#check SurrealExpLogSemantics.select_true_log
#check SurrealExpLogSemantics.select_true_hyperExp_zero
#check SurrealExpLogSemantics.select_true_hyperLog_zero
#check SurrealExpLogSemantics.nontrivial_select_iff
#check SurrealExpLogSemantics.not_nontrivial_select_iff
#check SurrealExpLogSemantics.toModel_select_false_exp
#check SurrealExpLogSemantics.toModel_select_false_log
#check SurrealExpLogSemantics.toModel_select_false_hyperExp
#check SurrealExpLogSemantics.toModel_select_false_hyperLog
#check SurrealExpLogSemantics.toModel_select_true_exp
#check SurrealExpLogSemantics.toModel_select_true_log
#check SurrealExpLogSemantics.toModel_select_true_hyperExp_zero
#check SurrealExpLogSemantics.toModel_select_true_hyperLog_zero
#check SurrealExpLogSemantics.toModel_select_true_hyperExp_succ
#check SurrealExpLogSemantics.toModel_select_true_hyperLog_succ
#check SurrealExpLogSemantics.toCore_identity
#check SurrealExpLogSemantics.toModel_identity_exp
#check SurrealExpLogSemantics.toModel_identity_log
#check SurrealExpLogSemantics.toModel_identity_hyperExp
#check SurrealExpLogSemantics.toModel_identity_hyperLog

end NameWiringSmoke

end
end Numbers
end Tests
end HeytingLean
