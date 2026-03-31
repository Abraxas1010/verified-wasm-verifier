import HeytingLean.Genesis.EigenformSoup.Invariants

/-!
# EigenformSoup JRatchet Bridge Regression

Theorem-level regression checks for the LES -> `Topos.JRatchet` bridge.
-/

namespace HeytingLean.Tests.Genesis
open HeytingLean.Genesis.EigenformSoup

theorem jRatchetTrajectory_bridge_regression {nuc : SoupNucleus} (s : SoupState nuc) :
    HeytingLean.Topos.JRatchet.RatchetTrajectory
      (fun fuel => jRatchetLevel (runSoupAux fuel s)) := by
  exact jRatchetTrajectory (nuc := nuc) s

theorem alignsWithJRatchetVocabulary_bridge_regression {nuc : SoupNucleus} (s : SoupState nuc) :
    alignsWithJRatchetVocabulary s := by
  exact alignsWithJRatchetVocabulary_intro (nuc := nuc) s

end HeytingLean.Tests.Genesis
