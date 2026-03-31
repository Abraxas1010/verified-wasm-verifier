import HeytingLean.Crypto.NECP.Protocol
import HeytingLean.NucleusDB.Security.Assumptions
import HeytingLean.NucleusDB.Security.Reductions

namespace HeytingLean
namespace Crypto
namespace NECP

open NRAExperiment
open NucleusDB.Security

section

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

abbrev Protocol := NECPProtocol (R := R) (M := M)
abbrev NRAAdversary (P : Protocol (R := R) (M := M)) := NRAExperiment.NRAAdversary P.toNRAExperiment

/-- An NECP adversary proposes a secret guess from the public observation. -/
structure NECPAdversary (P : Protocol (R := R) (M := M)) where
  queryBudget : Nat
  observe : Submodule R M → Submodule R M

namespace NECPAdversary

variable {P : Protocol (R := R) (M := M)}

/-- Breaking means recovering a guess whose published closure matches the hidden secret. -/
def Breaks (A : NECPAdversary P) : Prop :=
  ∀ secret, P.verifies (A.observe (P.publish secret)) secret

end NECPAdversary

/-- Backwards-compatible alias for the protocol-breaking interface. -/
abbrev ProtocolBreaker (P : Protocol (R := R) (M := M)) := NECPAdversary P

/-- NECP security means no breaker wins against the protocol surface. -/
def NECPSecure (P : Protocol (R := R) (M := M)) : Prop :=
  ¬ ∃ A : NECPAdversary P, A.Breaks

/-- Any NECP adversary induces an adversary for the NRA experiment. -/
def adversaryAsNRA (P : Protocol (R := R) (M := M))
    (A : NECPAdversary P) : NRAAdversary P where
  queryBudget := A.queryBudget
  solve := A.observe

theorem adversary_yields_nra_win (P : Protocol (R := R) (M := M))
    (A : NECPAdversary P) (hA : A.Breaks) :
    wins P.toNRAExperiment (adversaryAsNRA P A) := by
  intro secret
  exact hA secret

/-- Explicit reduction contract from protocol breakers to nucleus-recovery adversaries. -/
structure ObservationReduction (P : Protocol (R := R) (M := M)) where
  toNRA : NECPAdversary P → NRAAdversary P
  preservesBreaks :
    ∀ A : NECPAdversary P,
      A.Breaks → wins P.toNRAExperiment (toNRA A)

/-- The concrete reduction implemented by the protocol surface. -/
def protocolObservationReduction (P : Protocol (R := R) (M := M)) :
    ObservationReduction P where
  toNRA := adversaryAsNRA P
  preservesBreaks := adversary_yields_nra_win P

theorem nra_hard_implies_necp_secure (P : Protocol (R := R) (M := M))
    (hHard : Hard P.toNRAExperiment) :
    NECPSecure P := by
  let red := protocolObservationReduction P
  intro hBreak
  rcases hBreak with ⟨A, hA⟩
  exact hHard ⟨red.toNRA A, red.preservesBreaks A hA⟩

/-- Public reduction disclosure advertised by the abstract NECP security theorem. -/
def necpReductionContract : ReductionContract where
  claim := "NECP security reduces protocol breaking to nucleus recovery"
  assumption := Assumption.witnessUnforgeability
  lossBits := 1
  maxQueries := 1

theorem necpReductionContract_valid :
    necpReductionContract.Valid := by
  simp [necpReductionContract, ReductionContract.Valid]

end

end NECP
end Crypto
end HeytingLean
