import HeytingLean.Bridges.Nucleus.Extensions.Prenucleus
import HeytingLean.Bridges.Nucleus.Extensions.PrenucleusFrame
import HeytingLean.Bridges.Nucleus.Extensions.PrenucleusStabilization
import HeytingLean.Bridges.Nucleus.Extensions.DeMorganization
import HeytingLean.Bridges.Nucleus.Extensions.LawvereTierneyStrengthening
import HeytingLean.Bridges.Nucleus.Extensions.UniformCompletionNucleus
import HeytingLean.Bridges.Nucleus.Extensions.DragalinFrame
import HeytingLean.Bridges.Nucleus.Extensions.QuanticNucleus
import HeytingLean.Bridges.Nucleus.Extensions.NuclearAdjunction
import HeytingLean.Bridges.Nucleus.Extensions.InfinityChuScaffold

namespace HeytingLean
namespace Bridges
namespace Nucleus
namespace Extensions

inductive DeliveryStatus where
  | done
  | inProgress
  | blocked
  deriving Repr, DecidableEq

open DeliveryStatus

def d1_prenucleus : DeliveryStatus := .done

def d2_demorganization : DeliveryStatus := .done

def d3_lawvereTierney : DeliveryStatus := .done

def d4_uniformCompletion : DeliveryStatus := .done

def d5_dragalin : DeliveryStatus := .done

def d6_quantic : DeliveryStatus := .done

def d7_nuclearAdjunction : DeliveryStatus := .done

def d8_infinityChu : DeliveryStatus := .done

def allDeliverables : List (String × DeliveryStatus) :=
  [ ("D1 Prenucleus", d1_prenucleus)
  , ("D2 DeMorganization", d2_demorganization)
  , ("D3 Lawvere-Tierney", d3_lawvereTierney)
  , ("D4 UniformCompletion", d4_uniformCompletion)
  , ("D5 Dragalin", d5_dragalin)
  , ("D6 Quantic", d6_quantic)
  , ("D7 NuclearAdjunction", d7_nuclearAdjunction)
  , ("D8 InfinityChu", d8_infinityChu)
  ]

example : allDeliverables.length = 8 := by
  decide

theorem allDeliverables_done :
    ∀ entry ∈ allDeliverables, entry.snd = .done := by
  intro entry h
  simp [allDeliverables, d1_prenucleus, d2_demorganization, d3_lawvereTierney,
    d4_uniformCompletion, d5_dragalin, d6_quantic, d7_nuclearAdjunction, d8_infinityChu] at h
  rcases h with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · cases h1; rfl
  · cases h2; rfl
  · cases h3; rfl
  · cases h4; rfl
  · cases h5; rfl
  · cases h6; rfl
  · cases h7; rfl
  · cases h8; rfl

end Extensions
end Nucleus
end Bridges
end HeytingLean
