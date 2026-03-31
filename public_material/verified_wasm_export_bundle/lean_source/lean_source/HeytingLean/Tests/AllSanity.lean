import HeytingLean.Tests.Crypto.AllSanity
import HeytingLean.Tests.Crypto.SHA256PrimitivesSanity
import HeytingLean.Tests.Constructor.AllSanity
import HeytingLean.Tests.CPP.AllSanity
import HeytingLean.Tests.Security.AllSanity
import HeytingLean.Tests.QKD.BB84Tests
import HeytingLean.Tests.QKD.E91Tests
import HeytingLean.Tests.Contextuality.WitnessTests
import HeytingLean.Tests.PhotoemissionSanity
import HeytingLean.Tests.UnifiedMathSanity
import HeytingLean.Tests.LeanKernelSanity
import HeytingLean.Tests.TensorLogic.AllSanity
import HeytingLean.Tests.Homology.AllSanity
import HeytingLean.Tests.LoF.DifferentialSanity
import HeytingLean.Tests.TropicalSanity
import HeytingLean.Tests.ProgramCalculus.AllSanity
import HeytingLean.Tests.Integration.OrganicAlignmentStack
import HeytingLean.Tests.Compilation.CodegenSanity
import HeytingLean.Tests.UnifiedSystem.Sanity
import HeytingLean.Tests.Coalgebra.UniversalSanity
import HeytingLean.Tests.Ontology.CoinductiveBoundedSanity
import HeytingLean.Tests.Ontology.CoinductiveBoundedBridgeSanity
import HeytingLean.Tests.Ontology.CoinductiveBoundedObserverSanity
import HeytingLean.Tests.Ontology.CoinductiveBoundedKnotRoutingSanity
import HeytingLean.Tests.Ontology.CoinductiveBoundedBackendIndependenceSanity
import HeytingLean.Tests.Ontology.CoinductiveBoundedSKYCompilationSanity
import HeytingLean.Tests.Topos.LocSysSmoke
import HeytingLean.Tests.Equivalence.LogicMatrixCoalgebraSanity
import HeytingLean.Tests.Representations.MatrixSanity
import HeytingLean.Tests.Representations.RadialSanity
import HeytingLean.Tests.Silicon.AllSanity
import HeytingLean.Tests.Bridges.LEPMasterSprintSanity
import HeytingLean.Tests.Bridge.AlMayahi.TauCoordinationSanity
import HeytingLean.Tests.Layouts.AllSanity
import HeytingLean.Tests.Information.AllSanity
import HeytingLean.Tests.VETT.Sanity
import HeytingLean.Tests.VETT.PastingEvalSanity
import HeytingLean.Tests.PhysLean.ImportSanity
import HeytingLean.Tests.String.Sanity
import HeytingLean.Tests.String.WorldsheetSanity
import HeytingLean.Tests.String.PolyakovMVPSanity
import HeytingLean.Tests.Analysis.SpectralContractsSanity
import HeytingLean.Tests.Archetype.MagnitudeEigenformSanity
import HeytingLean.Tests.Archetype.MagnitudeBlurredPersistentSanity
import HeytingLean.Tests.Archetype.MagnitudeDiagonalitySanity
import HeytingLean.Tests.Archetype.MagnitudeHomologyGroupsSanity
import HeytingLean.Tests.Archetype.MagnitudeKunnethMVSanity
import HeytingLean.Tests.EpistemicCalculus.AllSanity
import HeytingLean.Tests.Discovery.AllSanity
import HeytingLean.Tests.Magma.AllSanity
import HeytingLean.Tests.PadicDecoupling.PadicSanity
import HeytingLean.Tests.Bridge.NoCoincidence.AllSanity
import HeytingLean.Tests.KernelAssurance.AllSanity

/-!
# Test umbrella: all sanity checks

This file is the designated “default build hook” for compile-time sanity tests.
It intentionally avoids piggybacking on narrow single-purpose sanity modules.
-/

namespace HeytingLean.Tests.AllSanity

-- Intentionally empty: importing the modules is the test.

end HeytingLean.Tests.AllSanity
