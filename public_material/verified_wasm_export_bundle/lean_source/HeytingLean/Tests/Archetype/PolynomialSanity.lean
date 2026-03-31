import HeytingLean.Bridges.Archetype.PolynomialToLens

open _root_.CategoryTheory.Polynomial

open HeytingLean.CategoryTheory.Polynomial

example (T : Type) (x : applyFun coreLensCarrierPoly T) :
    applyMap (polyid coreLensCarrierPoly) T x = x := by
  exact HeytingLean.Bridges.Archetype.polynomial_lens_id_on_core_state T x

example (T : Type) (x : applyFun coreLensCarrierPoly T) :
    applyMap (composemap (polyid coreLensCarrierPoly) (polyid coreLensCarrierPoly)) T x = x := by
  calc
    applyMap (composemap (polyid coreLensCarrierPoly) (polyid coreLensCarrierPoly)) T x
        = applyMap (polyid coreLensCarrierPoly) T (applyMap (polyid coreLensCarrierPoly) T x) := by
          exact HeytingLean.Bridges.Archetype.polynomial_lens_comp_on_core_state
            (polyid coreLensCarrierPoly) (polyid coreLensCarrierPoly) T x
    _ = x := by
      simp [HeytingLean.Bridges.Archetype.polynomial_lens_id_on_core_state]
