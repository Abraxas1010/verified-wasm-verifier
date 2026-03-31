import HeytingLean.Bridges.Nucleus.NucleusSheafGlue

namespace HeytingLean
namespace Bridges
namespace Nucleus

/-- All known nucleus variant kinds in HeytingLean. -/
inductive NucleusVariantTag where
  -- Tier 1: Core definitions
  | mathlibNucleus
  | coreNucleus
  | coreHeytingNucleus
  | ruleNucleus
  | calculusNucleus
  -- Tier 2: Interior nuclei
  | intNucleus
  | qgiNucleus
  -- Tier 3: Extended bundles
  | reentry
  | ctNucleus
  | bauerWorld
  -- Tier 4: Concrete instances
  | doubleNegNucleus
  | reluNucleus
  | unionNucleus
  | adjoinNucleus
  | equilibriumNucleus
  | collapseNucleus
  | periodicNucleus
  -- Tier 5: Nucleus-adjacent interfaces
  | nucleusHom
  | certifiedNucleus
  | nat1NucleusIR
  | rNucleusMonad
  | finiteAgentFamily
  -- Tier 6: Scaffold
  | modNucleus
  | qNucleus
  | tensorNucleus
  -- Tier 7: R nucleus extension lanes
  | prenucleus
  | deMorganizationNucleus
  | lawvereTierneyStrengthening
  | uniformCompletionNucleus
  | dragalinGeneratedNucleus
  | quanticNucleus
  | nuclearAdjunction
  | infinityChuNucleus
  -- Tier 8: Nucleus-named but not nucleus-typed
  | nucleusDB
  | reentryKernel
  | nucleusCommit
  deriving Repr, DecidableEq

def allNucleusTags : List NucleusVariantTag :=
  [ .mathlibNucleus
  , .coreNucleus
  , .coreHeytingNucleus
  , .ruleNucleus
  , .calculusNucleus
  , .intNucleus
  , .qgiNucleus
  , .reentry
  , .ctNucleus
  , .bauerWorld
  , .doubleNegNucleus
  , .reluNucleus
  , .unionNucleus
  , .adjoinNucleus
  , .equilibriumNucleus
  , .collapseNucleus
  , .periodicNucleus
  , .nucleusHom
  , .certifiedNucleus
  , .nat1NucleusIR
  , .rNucleusMonad
  , .finiteAgentFamily
  , .modNucleus
  , .qNucleus
  , .tensorNucleus
  , .prenucleus
  , .deMorganizationNucleus
  , .lawvereTierneyStrengthening
  , .uniformCompletionNucleus
  , .dragalinGeneratedNucleus
  , .quanticNucleus
  , .nuclearAdjunction
  , .infinityChuNucleus
  , .nucleusDB
  , .reentryKernel
  , .nucleusCommit
  ]

example : allNucleusTags.length = 36 := by
  decide

end Nucleus
end Bridges
end HeytingLean
