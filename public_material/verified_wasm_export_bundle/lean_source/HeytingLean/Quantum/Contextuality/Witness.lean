import HeytingLean.LoF.CryptoSheaf.Quantum.EmpiricalModel

/-!
# Contextuality witnesses (re-export layer)

This module provides a stable namespace `HeytingLean.Quantum.Contextuality.*` by re-exporting the
existing possibilistic contextuality infrastructure from `HeytingLean.LoF.CryptoSheaf.Quantum.*`.

The goal is to avoid churn while giving later crypto phases a clean dependency target.
-/

namespace HeytingLean
namespace Quantum
namespace Contextuality

open HeytingLean.LoF.CryptoSheaf.Quantum

abbrev Context := HeytingLean.LoF.CryptoSheaf.Quantum.Context
abbrev Assignment := HeytingLean.LoF.CryptoSheaf.Quantum.Assignment
abbrev EmpiricalModel := HeytingLean.LoF.CryptoSheaf.Quantum.EmpiricalModel
abbrev HasGlobalSection := HeytingLean.LoF.CryptoSheaf.Quantum.HasGlobalSection
abbrev NoGlobalSection := HeytingLean.LoF.CryptoSheaf.Quantum.NoGlobalSection

/-- A packaged contextuality witness: an empirical model on a cover with no global section. -/
structure Witness where
  X : Context
  cover : Finset Context
  e : EmpiricalModel cover
  coverSubX : ∀ {C}, C ∈ cover → C ⊆ X
  noGlobal : NoGlobalSection X cover e (fun {_} hC => coverSubX hC)

end Contextuality
end Quantum
end HeytingLean
