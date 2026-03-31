import HeytingLean.PTS.BaseExtension.Contextual.Context

namespace HeytingLean.PTS.BaseExtension.Contextual

mutual
  def encode : IPL → Goal
    | .atom p => Goal.atom (AtomVar.atom p)
    | .bot => Goal.all (Goal.atom (AtomVar.bvar 0))
    | .conj φ ψ =>
        Goal.all
          (Goal.imp
            (Goal.imp (encode φ) (Goal.imp (encode ψ) (Goal.atom (AtomVar.bvar 0))))
            (Goal.atom (AtomVar.bvar 0)))
    | .disj φ ψ =>
        Goal.all
          (Goal.imp
            (Goal.imp (encode φ) (Goal.atom (AtomVar.bvar 0)))
            (Goal.imp
              (Goal.imp (encode ψ) (Goal.atom (AtomVar.bvar 0)))
              (Goal.atom (AtomVar.bvar 0))))
    | .imp φ ψ => Goal.imp (encode φ) (encode ψ)
end

def encodeCtx (Γ : List IPL) : Program :=
  Γ.map encode

end Contextual
end HeytingLean.PTS.BaseExtension
