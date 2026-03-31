import PFR.ForMathlib.Entropy.Basic
import PFR.ForMathlib.Entropy.Kernel.MutualInfo
import PFR.ForMathlib.Entropy.Kernel.RuzsaDist
import PFR.ForMathlib.Entropy.Measure
import PFR.Kullback

/-!
# Teorth / PFR Entropy + Probability Bridge (Stable Import Set)

This module provides a **stable HeytingLean import path** for the information-theory /
probability-theory toolbox developed in teorth's PFR project.

Why this exists:
- HeytingLean wants to *use and index* PFR's entropy / mutual information / KL divergence lemmas
  as a reusable toolbox for Crypto/Quantum/Physics work.
- The PFR project depends (transitively) on external packages that may contain warnings (including
  proof placeholders). HeytingLean keeps **strict** builds for its core library, so this file is **not**
  imported by `HeytingLean.lean`. Instead, it is built/indexed in *non-strict* contexts.

Build policy:
- Strict core: `(cd lean && lake build --wfail)` (does not import this module)
- External bridge (non-strict): `(cd lean && lake build HeytingLean.External.Teorth.PFREntropyBridge)`

This file intentionally contains only small aliases and documentation; the heavy lifting lives in
the upstream PFR modules.
-/

namespace HeytingLean.External.Teorth.PFREntropyBridge

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology ProbabilityTheory

-- Small namespaced aliases so downstream HeytingLean code can refer to these without reopening
-- the upstream namespaces explicitly.
--
-- Important: we do *not* use the default-argument versions here (they rely on tactics such as
-- `volume_tac`), since that can get stuck when elaborating a standalone constant.
noncomputable abbrev entropy {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (X : Ω → S) (μ : Measure Ω) : ℝ :=
  ProbabilityTheory.entropy X μ

noncomputable abbrev condEntropy {Ω S T : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) : ℝ :=
  ProbabilityTheory.condEntropy X Y μ

noncomputable abbrev mutualInfo {Ω S T : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) : ℝ :=
  ProbabilityTheory.mutualInfo X Y μ

-- Kullback-Leibler divergence lives at the root namespace in teorth/PFR.
noncomputable abbrev KLDiv {Ω Ω' G : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace G]
    (X : Ω → G) (Y : Ω' → G) (μ : Measure Ω) (μ' : Measure Ω') : ℝ :=
  _root_.KLDiv X Y μ μ'

-- Re-export high-value PFR entropy/probability lemmas under a stable HeytingLean namespace.
export ProbabilityTheory.Kernel (chain_rule entropy_comap)
export ProbabilityTheory.IndepFun (entropy_pair_eq_add)
export ProbabilityTheory.IdentDistrib (mutualInfo_eq)

end HeytingLean.External.Teorth.PFREntropyBridge
