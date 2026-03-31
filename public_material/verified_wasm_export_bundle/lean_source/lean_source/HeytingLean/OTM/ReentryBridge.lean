import HeytingLean.OTM.Basic
import HeytingLean.PerspectivalPlenum.DirectConnection
import HeytingLean.LoF.Combinators.Topos.SieveNucleus

namespace HeytingLean
namespace OTM

open CategoryTheory

universe u v w

/--
OTM-facing bridge theorem:
re-entry fixedness is equivalent to Lawvere-Tierney reclassification fixedness.
-/
theorem otm_reentry_fixed_iff_lt_closed
    {Ωα : Type u} [LoF.PrimaryAlgebra Ωα]
    {C : Type v} [Category.{w} C]
    [CategoryTheory.Limits.HasPullbacks C]
    [CategoryTheory.HasClassifier C]
    (B : PerspectivalPlenum.ReentryLTBridge Ωα C) (p : Ωα) :
    B.R.nucleus p = p ↔
      Topos.LTfromNucleus.reclassify (C := C) B.ltKit.j (B.truthEquiv p) = B.truthEquiv p := by
  exact
    (PerspectivalPlenum.ReentryLTBridge.reentry_fixed_iff_reclassify_fixed (C := C) B p)

/--
OTM-facing bridge theorem:
re-entry fixedness is equivalent to `LocalOperator.IsClosed` at the classifier.
-/
theorem otm_reentry_fixed_iff_local_closed
    {Ωα : Type u} [LoF.PrimaryAlgebra Ωα]
    {C : Type v} [Category.{w} C]
    [CategoryTheory.Limits.HasPullbacks C]
    [CategoryTheory.HasClassifier C]
    (B : PerspectivalPlenum.ReentryLTBridge Ωα C) (p : Ωα) :
    B.R.nucleus p = p ↔
      Topos.LocalOperator.IsClosed
        (C := C) (PerspectivalPlenum.ReentryLTBridge.localOperator (C := C) B) (B.truthEquiv p) := by
  exact
    (PerspectivalPlenum.ReentryLTBridge.reentry_fixed_iff_isClosed_omega (C := C) B p)

/--
Conditional bridge to Grothendieck closure:
if the local-operator closedness witness transports to a Grothendieck closed sieve,
then re-entry fixedness is equivalent to Grothendieck closedness.
-/
theorem otm_reentry_fixed_iff_groth_closed_of_transport
    {Ωα : Type u} [LoF.PrimaryAlgebra Ωα]
    {C : Type v} [Category.{w} C]
    [CategoryTheory.Limits.HasPullbacks C]
    [CategoryTheory.HasClassifier C]
    (B : PerspectivalPlenum.ReentryLTBridge Ωα C)
    (J : CategoryTheory.GrothendieckTopology C)
    {X : C} (S : CategoryTheory.Sieve X) (p : Ωα)
    (htransport :
      Topos.LocalOperator.IsClosed
        (C := C) (PerspectivalPlenum.ReentryLTBridge.localOperator (C := C) B) (B.truthEquiv p)
        ↔ J.IsClosed S) :
    B.R.nucleus p = p ↔ J.IsClosed S := by
  exact (otm_reentry_fixed_iff_local_closed (C := C) B p).trans htransport

/--
Fixed-point form of the same transport: re-entry fixedness corresponds to fixed
points of the Grothendieck sieve nucleus under the supplied transport witness.
-/
theorem otm_reentry_fixed_iff_sieve_nucleus_fixed_of_transport
    {Ωα : Type u} [LoF.PrimaryAlgebra Ωα]
    {C : Type v} [Category.{w} C]
    [CategoryTheory.Limits.HasPullbacks C]
    [CategoryTheory.HasClassifier C]
    (B : PerspectivalPlenum.ReentryLTBridge Ωα C)
    (J : CategoryTheory.GrothendieckTopology C)
    {X : C} (S : CategoryTheory.Sieve X) (p : Ωα)
    (htransport :
      Topos.LocalOperator.IsClosed
        (C := C) (PerspectivalPlenum.ReentryLTBridge.localOperator (C := C) B) (B.truthEquiv p)
        ↔ J.IsClosed S) :
    B.R.nucleus p = p ↔
      S ∈ HeytingLean.LoF.Combinators.Heyting.FixedPoints
        (HeytingLean.LoF.Combinators.Topos.sieveNucleus (C := C) J X) := by
  calc
    B.R.nucleus p = p ↔ J.IsClosed S :=
      otm_reentry_fixed_iff_groth_closed_of_transport (C := C) B J S p htransport
    _ ↔ S ∈ HeytingLean.LoF.Combinators.Heyting.FixedPoints
          (HeytingLean.LoF.Combinators.Topos.sieveNucleus (C := C) J X) :=
      (LoF.Combinators.Topos.mem_fixedPoints_sieveNucleus_iff_isClosed (C := C) (J := J) (S := S)).symm

/--
Direct correspondence for queue edge:
R-nucleus fixedness/LT/local-closedness package <-> ontological reentry-LT bridge.
-/
theorem thm_sheaf_glue_r_nucleus_re_entry_fixedness_lt_local_operator_closedness_to_ontological_driver_reentryltbridge
    {Ωα : Type u} [LoF.PrimaryAlgebra Ωα]
    {C : Type v} [Category.{w} C]
    [CategoryTheory.Limits.HasPullbacks C]
    [CategoryTheory.HasClassifier C]
    (B : PerspectivalPlenum.ReentryLTBridge Ωα C) (p : Ωα) :
    (B.R.nucleus p = p ↔
      Topos.LTfromNucleus.reclassify (C := C) B.ltKit.j (B.truthEquiv p) = B.truthEquiv p) ∧
    (B.R.nucleus p = p ↔
      Topos.LocalOperator.IsClosed
        (C := C) (PerspectivalPlenum.ReentryLTBridge.localOperator (C := C) B) (B.truthEquiv p)) := by
  exact ⟨
    otm_reentry_fixed_iff_lt_closed (C := C) B p,
    otm_reentry_fixed_iff_local_closed (C := C) B p
  ⟩

/--
Reverse direct correspondence for queue edge:
ontological reentry-LT bridge <-> R-nucleus fixedness/LT/local-closedness package.
-/
theorem thm_sheaf_glue_ontological_driver_reentryltbridge_to_r_nucleus_re_entry_fixedness_lt_local_operator_closedness
    {Ωα : Type u} [LoF.PrimaryAlgebra Ωα]
    {C : Type v} [Category.{w} C]
    [CategoryTheory.Limits.HasPullbacks C]
    [CategoryTheory.HasClassifier C]
    (B : PerspectivalPlenum.ReentryLTBridge Ωα C) (p : Ωα) :
    (B.R.nucleus p = p ↔
      Topos.LTfromNucleus.reclassify (C := C) B.ltKit.j (B.truthEquiv p) = B.truthEquiv p) ∧
    (B.R.nucleus p = p ↔
      Topos.LocalOperator.IsClosed
        (C := C) (PerspectivalPlenum.ReentryLTBridge.localOperator (C := C) B) (B.truthEquiv p)) := by
  exact
    thm_sheaf_glue_r_nucleus_re_entry_fixedness_lt_local_operator_closedness_to_ontological_driver_reentryltbridge
      (C := C) B p

/--
Direct correspondence for queue edge:
R-nucleus fixedness/LT/local-closedness package <-> ontological topos-bridge reentry-LT driver.
-/
theorem thm_sheaf_glue_r_nucleus_re_entry_fixedness_lt_local_operator_closedness_to_ontological_driver_topos_ontology_bridge_reentryltbridge
    {Ωα : Type u} [LoF.PrimaryAlgebra Ωα]
    {C : Type v} [Category.{w} C]
    [CategoryTheory.Limits.HasPullbacks C]
    [CategoryTheory.HasClassifier C]
    (B : PerspectivalPlenum.ReentryLTBridge Ωα C) (p : Ωα) :
    (B.R.nucleus p = p ↔
      Topos.LTfromNucleus.reclassify (C := C) B.ltKit.j (B.truthEquiv p) = B.truthEquiv p) ∧
    (B.R.nucleus p = p ↔
      Topos.LocalOperator.IsClosed
        (C := C) (PerspectivalPlenum.ReentryLTBridge.localOperator (C := C) B) (B.truthEquiv p)) := by
  exact
    thm_sheaf_glue_r_nucleus_re_entry_fixedness_lt_local_operator_closedness_to_ontological_driver_reentryltbridge
      (C := C) B p

/--
Reverse direct correspondence for queue edge:
ontological topos-bridge reentry-LT driver <-> R-nucleus fixedness/LT/local-closedness package.
-/
theorem thm_sheaf_glue_ontological_driver_topos_ontology_bridge_reentryltbridge_to_r_nucleus_re_entry_fixedness_lt_local_operator_closedness
    {Ωα : Type u} [LoF.PrimaryAlgebra Ωα]
    {C : Type v} [Category.{w} C]
    [CategoryTheory.Limits.HasPullbacks C]
    [CategoryTheory.HasClassifier C]
    (B : PerspectivalPlenum.ReentryLTBridge Ωα C) (p : Ωα) :
    (B.R.nucleus p = p ↔
      Topos.LTfromNucleus.reclassify (C := C) B.ltKit.j (B.truthEquiv p) = B.truthEquiv p) ∧
    (B.R.nucleus p = p ↔
      Topos.LocalOperator.IsClosed
        (C := C) (PerspectivalPlenum.ReentryLTBridge.localOperator (C := C) B) (B.truthEquiv p)) := by
  exact
    thm_sheaf_glue_r_nucleus_re_entry_fixedness_lt_local_operator_closedness_to_ontological_driver_topos_ontology_bridge_reentryltbridge
      (C := C) B p

/--
Direct correspondence for queue edge:
R-nucleus fixedness/LT/local-closedness package <-> ontological Grothendieck-closure-as-nucleus driver.
-/
theorem thm_sheaf_glue_r_nucleus_re_entry_fixedness_lt_local_operator_closedness_to_ontological_driver_grothendieck_closure_as_nucleus_j_close
    {Ωα : Type u} [LoF.PrimaryAlgebra Ωα]
    {C : Type v} [Category.{w} C]
    [CategoryTheory.Limits.HasPullbacks C]
    [CategoryTheory.HasClassifier C]
    (B : PerspectivalPlenum.ReentryLTBridge Ωα C)
    (J : CategoryTheory.GrothendieckTopology C)
    {X : C} (S : CategoryTheory.Sieve X) (p : Ωα)
    (htransport :
      Topos.LocalOperator.IsClosed
        (C := C) (PerspectivalPlenum.ReentryLTBridge.localOperator (C := C) B) (B.truthEquiv p)
        ↔ J.IsClosed S) :
    B.R.nucleus p = p ↔
      S ∈ HeytingLean.LoF.Combinators.Heyting.FixedPoints
        (HeytingLean.LoF.Combinators.Topos.sieveNucleus (C := C) J X) := by
  exact
    otm_reentry_fixed_iff_sieve_nucleus_fixed_of_transport (C := C) B J S p htransport

/--
Reverse direct correspondence for queue edge:
ontological Grothendieck-closure-as-nucleus driver <-> R-nucleus fixedness/LT/local-closedness package.
-/
theorem thm_sheaf_glue_ontological_driver_grothendieck_closure_as_nucleus_j_close_to_r_nucleus_re_entry_fixedness_lt_local_operator_closedness
    {Ωα : Type u} [LoF.PrimaryAlgebra Ωα]
    {C : Type v} [Category.{w} C]
    [CategoryTheory.Limits.HasPullbacks C]
    [CategoryTheory.HasClassifier C]
    (B : PerspectivalPlenum.ReentryLTBridge Ωα C)
    (J : CategoryTheory.GrothendieckTopology C)
    {X : C} (S : CategoryTheory.Sieve X) (p : Ωα)
    (htransport :
      Topos.LocalOperator.IsClosed
        (C := C) (PerspectivalPlenum.ReentryLTBridge.localOperator (C := C) B) (B.truthEquiv p)
        ↔ J.IsClosed S) :
    B.R.nucleus p = p ↔
      S ∈ HeytingLean.LoF.Combinators.Heyting.FixedPoints
        (HeytingLean.LoF.Combinators.Topos.sieveNucleus (C := C) J X) := by
  exact
    thm_sheaf_glue_r_nucleus_re_entry_fixedness_lt_local_operator_closedness_to_ontological_driver_grothendieck_closure_as_nucleus_j_close
      (C := C) B J S p htransport

/--
Direct correspondence for queue edge:
ontological Grothendieck-closure driver <-> ontological topos reentry-LT bridge driver.
-/
theorem thm_sheaf_glue_ontological_driver_grothendieck_closure_as_nucleus_j_close_to_ontological_driver_topos_ontology_bridge_reentryltbridge
    {Ωα : Type u} [LoF.PrimaryAlgebra Ωα]
    {C : Type v} [Category.{w} C]
    [CategoryTheory.Limits.HasPullbacks C]
    [CategoryTheory.HasClassifier C]
    (B : PerspectivalPlenum.ReentryLTBridge Ωα C)
    (J : CategoryTheory.GrothendieckTopology C)
    {X : C} (S : CategoryTheory.Sieve X) (p : Ωα)
    (htransport :
      Topos.LocalOperator.IsClosed
        (C := C) (PerspectivalPlenum.ReentryLTBridge.localOperator (C := C) B) (B.truthEquiv p)
        ↔ J.IsClosed S) :
    B.R.nucleus p = p ↔
      S ∈ HeytingLean.LoF.Combinators.Heyting.FixedPoints
        (HeytingLean.LoF.Combinators.Topos.sieveNucleus (C := C) J X) := by
  exact
    thm_sheaf_glue_r_nucleus_re_entry_fixedness_lt_local_operator_closedness_to_ontological_driver_grothendieck_closure_as_nucleus_j_close
      (C := C) B J S p htransport

/--
Direct correspondence for queue edge:
ontological Grothendieck-closure driver <-> ontological reentry-LT bridge driver.
-/
theorem thm_sheaf_glue_ontological_driver_grothendieck_closure_as_nucleus_j_close_to_ontological_driver_reentryltbridge
    {Ωα : Type u} [LoF.PrimaryAlgebra Ωα]
    {C : Type v} [Category.{w} C]
    [CategoryTheory.Limits.HasPullbacks C]
    [CategoryTheory.HasClassifier C]
    (B : PerspectivalPlenum.ReentryLTBridge Ωα C)
    (J : CategoryTheory.GrothendieckTopology C)
    {X : C} (S : CategoryTheory.Sieve X) (p : Ωα)
    (htransport :
      Topos.LocalOperator.IsClosed
        (C := C) (PerspectivalPlenum.ReentryLTBridge.localOperator (C := C) B) (B.truthEquiv p)
        ↔ J.IsClosed S) :
    B.R.nucleus p = p ↔
      S ∈ HeytingLean.LoF.Combinators.Heyting.FixedPoints
        (HeytingLean.LoF.Combinators.Topos.sieveNucleus (C := C) J X) := by
  exact
    thm_sheaf_glue_r_nucleus_re_entry_fixedness_lt_local_operator_closedness_to_ontological_driver_grothendieck_closure_as_nucleus_j_close
      (C := C) B J S p htransport

/--
Reverse direct correspondence for queue edge:
ontological topos reentry-LT bridge driver <-> ontological Grothendieck-closure driver.
-/
theorem thm_sheaf_glue_ontological_driver_topos_ontology_bridge_reentryltbridge_to_ontological_driver_grothendieck_closure_as_nucleus_j_close
    {Ωα : Type u} [LoF.PrimaryAlgebra Ωα]
    {C : Type v} [Category.{w} C]
    [CategoryTheory.Limits.HasPullbacks C]
    [CategoryTheory.HasClassifier C]
    (B : PerspectivalPlenum.ReentryLTBridge Ωα C)
    (J : CategoryTheory.GrothendieckTopology C)
    {X : C} (S : CategoryTheory.Sieve X) (p : Ωα)
    (htransport :
      Topos.LocalOperator.IsClosed
        (C := C) (PerspectivalPlenum.ReentryLTBridge.localOperator (C := C) B) (B.truthEquiv p)
        ↔ J.IsClosed S) :
    B.R.nucleus p = p ↔
      S ∈ HeytingLean.LoF.Combinators.Heyting.FixedPoints
        (HeytingLean.LoF.Combinators.Topos.sieveNucleus (C := C) J X) := by
  exact
    thm_sheaf_glue_ontological_driver_grothendieck_closure_as_nucleus_j_close_to_ontological_driver_topos_ontology_bridge_reentryltbridge
      (C := C) B J S p htransport

/--
Direct correspondence for queue edge:
ontological topos reentry-LT bridge driver <-> ontological reentry-LT bridge driver.
-/
theorem thm_sheaf_glue_ontological_driver_topos_ontology_bridge_reentryltbridge_to_ontological_driver_reentryltbridge
    {Ωα : Type u} [LoF.PrimaryAlgebra Ωα]
    {C : Type v} [Category.{w} C]
    [CategoryTheory.Limits.HasPullbacks C]
    [CategoryTheory.HasClassifier C]
    (B : PerspectivalPlenum.ReentryLTBridge Ωα C) (p : Ωα) :
    (B.R.nucleus p = p ↔
      Topos.LTfromNucleus.reclassify (C := C) B.ltKit.j (B.truthEquiv p) = B.truthEquiv p) ∧
    (B.R.nucleus p = p ↔
      Topos.LocalOperator.IsClosed
        (C := C) (PerspectivalPlenum.ReentryLTBridge.localOperator (C := C) B) (B.truthEquiv p)) := by
  exact
    thm_sheaf_glue_r_nucleus_re_entry_fixedness_lt_local_operator_closedness_to_ontological_driver_topos_ontology_bridge_reentryltbridge
      (C := C) B p

/--
Reverse direct correspondence for queue edge:
ontological reentry-LT bridge driver <-> ontological Grothendieck-closure driver.
-/
theorem thm_sheaf_glue_ontological_driver_reentryltbridge_to_ontological_driver_grothendieck_closure_as_nucleus_j_close
    {Ωα : Type u} [LoF.PrimaryAlgebra Ωα]
    {C : Type v} [Category.{w} C]
    [CategoryTheory.Limits.HasPullbacks C]
    [CategoryTheory.HasClassifier C]
    (B : PerspectivalPlenum.ReentryLTBridge Ωα C)
    (J : CategoryTheory.GrothendieckTopology C)
    {X : C} (S : CategoryTheory.Sieve X) (p : Ωα)
    (htransport :
      Topos.LocalOperator.IsClosed
        (C := C) (PerspectivalPlenum.ReentryLTBridge.localOperator (C := C) B) (B.truthEquiv p)
        ↔ J.IsClosed S) :
    B.R.nucleus p = p ↔
      S ∈ HeytingLean.LoF.Combinators.Heyting.FixedPoints
        (HeytingLean.LoF.Combinators.Topos.sieveNucleus (C := C) J X) := by
  exact
    thm_sheaf_glue_ontological_driver_grothendieck_closure_as_nucleus_j_close_to_ontological_driver_reentryltbridge
      (C := C) B J S p htransport

/--
Direct correspondence for queue edge:
ontological reentry-LT bridge driver <-> ontological topos reentry-LT bridge driver.
-/
theorem thm_sheaf_glue_ontological_driver_reentryltbridge_to_ontological_driver_topos_ontology_bridge_reentryltbridge
    {Ωα : Type u} [LoF.PrimaryAlgebra Ωα]
    {C : Type v} [Category.{w} C]
    [CategoryTheory.Limits.HasPullbacks C]
    [CategoryTheory.HasClassifier C]
    (B : PerspectivalPlenum.ReentryLTBridge Ωα C) (p : Ωα) :
    (B.R.nucleus p = p ↔
      Topos.LTfromNucleus.reclassify (C := C) B.ltKit.j (B.truthEquiv p) = B.truthEquiv p) ∧
    (B.R.nucleus p = p ↔
      Topos.LocalOperator.IsClosed
        (C := C) (PerspectivalPlenum.ReentryLTBridge.localOperator (C := C) B) (B.truthEquiv p)) := by
  exact
    thm_sheaf_glue_ontological_driver_topos_ontology_bridge_reentryltbridge_to_ontological_driver_reentryltbridge
      (C := C) B p

end OTM
end HeytingLean
