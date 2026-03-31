import HeytingLean.Embeddings.PerspectivalDescentCarrier
import HeytingLean.Embeddings.PerspectivalDescentHierarchy
import HeytingLean.Embeddings.PDCExtensions
import HeytingLean.Embeddings.Adelic
import HeytingLean.Embeddings.AdelicInstances
import HeytingLean.Embeddings.GenericCrossLensTransport
import HeytingLean.ActiveInference.AdelicFreeEnergy
import HeytingLean.Renormalization.Adelic
import HeytingLean.ProgramCalculus.AdelicOps
import HeytingLean.ATP.DifferentiableATP.SheafTransport
import HeytingLean.PerspectivalPlenum.SheafLensCategory
import HeytingLean.PerspectivalPlenum.CechCohomology
import HeytingLean.PerspectivalPlenum.PDCDescentBridge
import HeytingLean.LoF.CryptoSheaf.Descent
import HeytingLean.LoF.Combinators.InfinityGroupoid.SSet
import HeytingLean.LoF.Combinators.Category.OmegaTowerLimit
import HeytingLean.LoF.Combinators.Category.OmegaTowerLimitGroupoid
import HeytingLean.GU.Groupoids
import HeytingLean.CategoryTheory.Fibred.GrothendieckOpfibration
import HeytingLean.GU.Bundles
import HeytingLean.GU.Connections

/-!
# Embeddings.PDCOverview

`PerspectivalDescentCarrier` (PDC) is the shared name for a recurring pattern in
HeytingLean:

1. perspective-indexed local carriers,
2. adelic-style finiteness (only finitely many non-integral perspectives),
3. transport/gluing across perspectives,
4. finite-precision truncation.

This module is documentation-only and ties together the five concrete families:

- Family A (adelic carriers): `Embeddings.Adelic`, `AdelicInstances`,
  `ActiveInference.AdelicFreeEnergy`, `Renormalization.Adelic`,
  `ProgramCalculus.AdelicOps`.
- Family B (transport/projection): `GenericCrossLensTransport`,
  `ATP.DifferentiableATP.SheafTransport`.
- Family C (∞-groupoid / higher): `InfinityGroupoid.SSet`,
  `OmegaTowerLimit`, `OmegaTowerLimitGroupoid`, `GU.Groupoids`.
- Family D (sheaf/descent): `SheafLensCategory`, `CechCohomology`,
  `CryptoSheaf.Descent`, `PerspectivalPlenum.PDCDescentBridge`.
- Family E (fibration/bundle): `CategoryTheory.Fibred.GrothendieckOpfibration`,
  `GU.Bundles`, `GU.Connections`.

Extension hierarchy:
- Level 1: `PerspectivalDescentCarrier`
- Level 2: `PDCWithTransport`
- Level 3: `PDCWithDescent`

Additional extension families (F-J) are provided in `Embeddings.PDCExtensions`:
- F: filtration/stratification carriers
- G: multi-realization carriers
- H: condensed/analytic carriers
- I: topological field theory carriers
- J: derived/higher categorical carriers

The intended workflow is:
`local perspective data -> transport cocycles -> matching-family descent -> global section`.
-/

namespace HeytingLean
namespace Embeddings

end Embeddings
end HeytingLean
