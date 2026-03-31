import HeytingLean.PTS.BaseExtension.IPL
import HeytingLean.PTS.BaseExtension.Search

namespace HeytingLean.PTS.BaseExtension

mutual
/--
`goalToDefinite` is the current scaffold collapse from the full HH goal language
into the definite-clause fragment. It is intentionally lossy for the continuation
shapes introduced by the CPS encoding, which is why the full Support=Search bridge
remains open.
-/
  def goalToDefinite : Goal → Definite
    | .atom v => Definite.atom v
    | .imp _ g => Definite.imp g (AtomVar.bvar 0)
    | .conj g₁ g₂ => Definite.conj (goalToDefinite g₁) (goalToDefinite g₂)
    | .disj g₁ g₂ => Definite.conj (goalToDefinite g₁) (goalToDefinite g₂)
    | .all g => Definite.all (goalToDefinite g)

  def encode : IPL → Goal
    | .atom p => Goal.atom (AtomVar.atom p)
    | .bot => Goal.all (Goal.atom (AtomVar.bvar 0))
    | .conj φ ψ =>
        Goal.all
          (Goal.imp
            (Definite.imp
              (Goal.imp (encodeD φ) (Goal.imp (encodeD ψ) (Goal.atom (AtomVar.bvar 0))))
              (AtomVar.bvar 0))
            (Goal.atom (AtomVar.bvar 0)))
    | .disj φ ψ =>
        Goal.all
          (Goal.imp
            (Definite.imp
              (Goal.imp (encodeD φ) (Goal.atom (AtomVar.bvar 0)))
              (AtomVar.bvar 0))
            (Goal.imp
              (Definite.imp
                (Goal.imp (encodeD ψ) (Goal.atom (AtomVar.bvar 0)))
                (AtomVar.bvar 0))
              (Goal.atom (AtomVar.bvar 0))))
    | .imp φ ψ => Goal.imp (encodeD φ) (encode ψ)

  def encodeD : IPL → Definite
    | .atom p => Definite.atom (.atom p)
    | .bot => Definite.absurd
    | .conj φ ψ => Definite.conj (encodeD φ) (encodeD ψ)
    | .imp φ (.atom p) => Definite.imp (encode φ) (.atom p)
    | φ => goalToDefinite (encode φ)
end

mutual
  def encodedGoalSize : Goal → Nat
    | .atom _ => 1
    | .imp d g => 1 + encodedDefiniteSize d + encodedGoalSize g
    | .conj g₁ g₂ => 1 + encodedGoalSize g₁ + encodedGoalSize g₂
    | .disj g₁ g₂ => 1 + encodedGoalSize g₁ + encodedGoalSize g₂
    | .all g => 1 + encodedGoalSize g

  def encodedDefiniteSize : Definite → Nat
    | .absurd => 1
    | .atom _ => 1
    | .imp g _ => 1 + encodedGoalSize g
    | .conj d₁ d₂ => 1 + encodedDefiniteSize d₁ + encodedDefiniteSize d₂
    | .all d => 1 + encodedDefiniteSize d
end

example : encodedGoalSize (encode (identityFormula ⟨0⟩)) > 0 := by
  native_decide

example : search 5 [] (encode (identityFormula ⟨0⟩)) = true := by
  native_decide

example : search 7 [] (encode (peirceFormula ⟨0⟩ ⟨1⟩)) = false := by
  native_decide

end HeytingLean.PTS.BaseExtension
