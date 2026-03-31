import HeytingLean.Crypto.KEM.MLKEM203Params
import HeytingLean.Crypto.KEM.MLKEMFailureBounds
import HeytingLean.Crypto.Lattice.CBDCounts
import HeytingLean.Crypto.Lattice.WindowedCounts

/-!
# ML-KEM failure probability: model skeleton + computed kernels

This file addresses the “scale-up” step for Gap 3 by defining:

- an explicit **bit-level model** for CBD samples (via `CBDCounts.cbdCounts`);
- an exact **product distribution** for products of two CBD samples (counts); and
- a scalable **sum-of-iid** machinery using convolution powering.

It also provides a *compatibility bridge* lemma showing how a computed model bound could discharge
the NIST inequality once the model is validated against the implementation.

Important limitations (tracked in the active conjecture/session):
- The real ML-KEM residual is not just a sum of iid products; it is structured by polynomial
  multiplication and uses concrete samplers.
- Computing exact distributions at full ML-KEM scale is expensive; this file focuses on the
  scalable infrastructure and small computed checks.
-/

namespace HeytingLean
namespace Crypto
namespace KEM
namespace FIPS203

open HeytingLean.Crypto.Lattice.CBDCounts

namespace FailureModel

/-- Product distribution (counts) for independent CBD samples with parameters `etaA` and `etaB`. -/
def cbdProductCounts (etaA etaB : Nat) : CenteredCounts := Id.run do
  let a := cbdCounts etaA
  let b := cbdCounts etaB
  let Bout := etaA * etaB
  let out0 := mkZero Bout
  let mut out := out0.data
  for i in [0:a.data.size] do
    for j in [0:b.data.size] do
      let zi := idxToInt a.B i
      let zj := idxToInt b.B j
      let z := zi * zj
      let idx := intToIdx Bout z
      if idx < out.size then
        out := out.set! idx (out[idx]! + a.data[i]! * b.data[j]!)
  return { B := Bout, data := out }

/-- Exact distribution of a sum of `terms` independent products of CBD samples. -/
def sumOfCBDProducts (etaA etaB terms : Nat) : CenteredCounts :=
  convolvePowFast (cbdProductCounts etaA etaB) terms

/-- Upper bound on `P(|sum| > T)` for a sum of products, encoded as an overflow count with window `T`. -/
def sumOfCBDProducts_tailUB (etaA etaB terms T : Nat) : Nat :=
  let base := HeytingLean.Crypto.Lattice.WindowedCounts.ofCenteredCounts T (cbdProductCounts etaA etaB)
  let d := HeytingLean.Crypto.Lattice.WindowedCounts.powUB base terms
  d.overflow

/-- A simplified one-coefficient residual model: `⟨e,r⟩ + e₂ - ⟨s,e₁⟩` as sums of iid products. -/
def residualCoeffModel (p : MLKEM203Params) : CenteredCounts :=
  let kn := p.k * p.n
  let dotER := sumOfCBDProducts p.eta1 p.eta1 kn
  let dotSE1 := sumOfCBDProducts p.eta1 p.eta2 kn
  let e2 := cbdCounts p.eta2
  convolve (convolve dotER e2) dotSE1

/-- Model failure event for a single coefficient: `|residual| > ⌊q/4⌋`. -/
def residualCoeffFailCount (p : MLKEM203Params) : Nat :=
  tailCount (residualCoeffModel p) (3329 / 4)

/-- Bridge lemma: if an implementation map matches the model, the model bound discharges NIST. -/
theorem failureProbability_lt_reported_of_model
    (failureProbability : MLKEM203Params → ℚ)
    (p : MLKEM203Params)
    (modelProbQ : ℚ)
    (hmodel : failureProbability p = modelProbQ)
    (hbound : modelProbQ < reportedFailureBoundQ p) :
    failureProbability p < reportedFailureBoundQ p := by
  simpa [hmodel] using hbound

/-!
## Small computed checks (sanity)

These are intentionally small: they verify the plumbing and ensure the computed kernel stays
executable under `--wfail`.
-/

def smallResidual : CenteredCounts :=
  residualCoeffModel { name := "toy", k := 1, n := 16, eta1 := 2, eta2 := 2, du := 10, dv := 4, ekSize := 0, dkSize := 0, ctSize := 0 }

theorem smallResidual_total_nonzero : totalCount smallResidual > 0 := by
  native_decide

theorem small_sumOfProducts_tailUB_sanity : sumOfCBDProducts_tailUB 2 2 64 50 * 2 ≤ 2 ^ (2 * (2 * 2) * 64) := by
  native_decide

end FailureModel

end FIPS203
end KEM
end Crypto
end HeytingLean
