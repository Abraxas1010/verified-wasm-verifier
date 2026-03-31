import HeytingLean.LoF.Synthesis.GrandCorrespondence
import HeytingLean.LoF.Synthesis.GrandCorrespondenceFull

/-!
# Smoke test: scoped “grand correspondence” snapshot

Compile-only checks that the synthesis module exposes the intended core artifacts.
-/

namespace HeytingLean
namespace Tests
namespace LoF

open HeytingLean.LoF

-- Generic kernel-quotient lemma
section Generic

universe u
variable {α : Type u} (close : α → α) (idem : ∀ x : α, close (close x) = close x)

#check Synthesis.KernelQuotient.closeQuotEquivRange (close := close) idem

end Generic

-- LoF⇄SKY soundness
section LoFSKY

open HeytingLean.LoF.Correspondence

variable {t u : LoFTerm}

#check Synthesis.Instances.lofSteps_sound (t := t) (u := u)

end LoFSKY

-- Full “Phase F” correspondence package
section Full

#check Synthesis.GrandCorrespondence

noncomputable def _grandCorrespondencePkg : Synthesis.GrandCorrespondence :=
  Synthesis.GrandCorrespondence.canonical

#check _grandCorrespondencePkg.sky_truncLStepsEquivStepsHom

end Full

end LoF
end Tests
end HeytingLean
