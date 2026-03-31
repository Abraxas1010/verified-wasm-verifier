import HeytingLean.Embeddings.Adelic
import HeytingLean.Embeddings.CoreLenses
import HeytingLean.Embeddings.LensIDCoreBridge

/-!
# Embeddings.AdelicInstances

Concrete `LensData` instances for the adelic carrier.

These are intentionally lightweight “first instantiations” that make the abstract
`AdelicRep` usable in executable demos without committing to a final choice of
per-lens completions/integrality/truncation.
-/

namespace HeytingLean
namespace Embeddings

/-- A tiny numeric `LensData` instance:

* completion at each lens is `Nat`,
* integrality means “is 0”,
* truncation clamps values to `≤ prec` (a cheap finite-precision approximation).

This is useful as a baseline for “lens depth profiles” and other metrics. -/
def natLensData : LensData where
  Completion := fun _ => Nat
  Integral := fun _ => { n | n = 0 }
  truncate := fun _ prec n => Nat.min n prec

/-- A tiny “lens prime” assignment (used for modular truncation demos). -/
def lensPrime : LensID → Nat
  | .omega => 2
  | .region => 3
  | .graph => 5
  | .clifford => 7
  | .tensor => 11
  | .topology => 13
  | .matula => 17

theorem lensPrime_pos (lens : LensID) : 0 < lensPrime lens := by
  cases lens <;> decide

/-- A lightweight `LensData` instance with `Int` components and lens-specific modular truncation.

This is **not** a full p-adic completion; it is a cheap, executable-friendly proxy that still
captures the “different scales have different truncation granularities” intuition. -/
def modIntLensData : LensData where
  Completion := fun _ => Int
  Integral := fun lens => { n : Int | n % (lensPrime lens : Int) = 0 }
  truncate := fun lens prec n =>
    let p : Int := (lensPrime lens : Int)
    n % (p ^ prec)

/-- Alias for the “modular `Int`” proxy, matching the WIP naming. -/
def padicStyleLensData : LensData :=
  modIntLensData

/-- A `LensData` whose components are taken in a coefficient semiring `K`.

This is a lightweight instance used for (e.g.) differential layer coefficients: there is no
truncation, and “integral” is taken to mean “exactly zero”. -/
def formalSumLensData (K : Type) [CommSemiring K] : LensData where
  Completion := fun _ => K
  Integral := fun _ => ({0} : Set K)
  truncate := fun _ _ k => k

/-- Extract `prec` many base-`lensPrime lens` digits (least-significant first) from a natural. -/
def padicDigitsNat (lens : LensID) (n : Nat) (prec : Nat) : List (Fin (lensPrime lens)) := by
  classical
  let p : Nat := lensPrime lens
  have hp : 0 < p := lensPrime_pos lens
  let rec go (n : Nat) : Nat → List (Fin p)
    | 0 => []
    | Nat.succ k =>
        let d : Fin p := ⟨n % p, Nat.mod_lt _ hp⟩
        d :: go (n / p) k
  exact (go n prec)

/-- Extract `prec` many base-`lensPrime lens` digits from an integer (via `natAbs`). -/
def padicDigits (lens : LensID) (n : Int) (prec : Nat) : List (Fin (lensPrime lens)) :=
  padicDigitsNat (lens := lens) n.natAbs prec

/-! ## CoreLensTag-scale adelic data (100-lens upgrade) -/

/-- Category-specific scaling factor used in the 100-lens adelic numeric encoding. -/
def coreCategoryScale : CoreLensTag.Category → Int
  | .foundational => 2
  | .generative => 3
  | .quantum => 5
  | .algebraic => 7
  | .process => 11
  | .crypto => 13
  | .physical => 17
  | .topological => 19
  | .information => 23
  | .bridge => 29
  | .pcb => 31
  | .economic => 37
  | .representation => 41
  | .utility => 43
  | .diffGeometry => 47
  | .tda => 53
  | .coalgebraic => 59
  | .optTransport => 61
  | .signal => 67

/-- Per-category completion carrier for the 100-lens package (uniform numeric encoding). -/
def coreCategoryCompletion : CoreLensTag.Category → Type
  | _ => Int

/-- Canonical/integral subsets for each core lens category. -/
def coreCategoryIntegral (c : CoreLensTag.Category) : Set Int :=
  { n : Int | n % coreCategoryScale c = 0 }

/-- Category-level truncation operators used by `coreLensData`. -/
def coreCategoryTruncate (c : CoreLensTag.Category) : Nat → Int → Int :=
  fun prec n => n % (coreCategoryScale c * Int.ofNat (prec + 1))

/-- 100-lens adelic data package keyed by `CoreLensTag`. -/
def coreLensData : GenericLensData.GenericLensData CoreLensTag where
  Completion tag := coreCategoryCompletion (CoreLensTag.categoryOf tag)
  Integral tag := coreCategoryIntegral (CoreLensTag.categoryOf tag)
  truncate tag := coreCategoryTruncate (CoreLensTag.categoryOf tag)

/-- Core 100-lens package is a concrete PDC instance. -/
instance : PerspectivalDescentCarrier CoreLensTag coreLensData.Completion where
  integral := coreLensData.Integral
  truncate := coreLensData.truncate
  finiteness x := by
    refine (Finset.finite_toSet (s := CoreLensTag.all.toFinset)).subset ?_
    intro tag _
    simpa using (List.mem_toFinset.mpr (CoreLensTag.mem_all tag))

/-- Compatibility view of `coreLensData` restricted to legacy `LensID` tags. -/
def coreLensDataOnLensID : GenericLensData.GenericLensData LensID where
  Completion lens := coreLensData.Completion (LensIDCoreBridge.toCoreLensTag lens)
  Integral lens := coreLensData.Integral (LensIDCoreBridge.toCoreLensTag lens)
  truncate lens := coreLensData.truncate (LensIDCoreBridge.toCoreLensTag lens)

/-- Legacy-view projection package remains a concrete PDC instance. -/
instance : PerspectivalDescentCarrier LensID coreLensDataOnLensID.Completion where
  integral := coreLensDataOnLensID.Integral
  truncate := coreLensDataOnLensID.truncate
  finiteness x := by
    refine
      (Finset.finite_toSet (s :=
        ({LensID.omega, LensID.region, LensID.graph, LensID.clifford,
          LensID.tensor, LensID.topology, LensID.matula} : Finset LensID))).subset ?_
    intro lens _
    cases lens <;> simp

/-- Backward-compatibility map: project a `CoreLensTag` adelic element onto legacy `LensID`. -/
def restrictCoreAdelicToLensID (x : GenericAdelicRep coreLensData) :
    GenericAdelicRep coreLensDataOnLensID := by
  refine ⟨fun lens => x.1 (LensIDCoreBridge.toCoreLensTag lens), ?_⟩
  refine Filter.eventually_cofinite.2 ?_
  refine
    (Finset.finite_toSet (s := ({LensID.omega, LensID.region, LensID.graph, LensID.clifford,
      LensID.tensor, LensID.topology, LensID.matula} : Finset LensID))).subset ?_
  intro lens _
  cases lens <;> simp

@[simp] theorem restrictCoreAdelicToLensID_apply (x : GenericAdelicRep coreLensData) (lens : LensID) :
    (restrictCoreAdelicToLensID x).1 lens = x.1 (LensIDCoreBridge.toCoreLensTag lens) := rfl

end Embeddings
end HeytingLean
