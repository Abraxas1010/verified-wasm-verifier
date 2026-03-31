import HeytingLean.Embeddings.PDCExtensions.CondensedAnalytic

namespace HeytingLean
namespace Topology
namespace Condensed

abbrev CondensedTestObj := Embeddings.PDCExtensions.CondensedTestObj
abbrev LiquidValue := Embeddings.PDCExtensions.LiquidValue

/-- Truncation at precision 0 yields the integral value in the condensed PDC model. -/
theorem truncate_zero (t : CondensedTestObj) (x : Int) :
    Embeddings.PerspectivalDescentCarrier.truncate
        (τ := CondensedTestObj) (Carrier := fun _ => Int) t 0 x = 0 :=
  Embeddings.PDCExtensions.condensed_truncate_zero t x

/-- Liquid truncation never increases the stored norm. -/
theorem liquid_truncate_norm_le (t : CondensedTestObj) (k : Nat) (x : LiquidValue) :
    (Embeddings.PerspectivalDescentCarrier.truncate
      (τ := CondensedTestObj) (Carrier := fun _ => LiquidValue) t k x).norm ≤ k :=
  Embeddings.PDCExtensions.liquid_truncate_norm_le t k x

/-- The condensed test-object universe is finite. -/
instance finite_test_object_universe : Fintype CondensedTestObj := by
  infer_instance

end Condensed
end Topology
end HeytingLean
