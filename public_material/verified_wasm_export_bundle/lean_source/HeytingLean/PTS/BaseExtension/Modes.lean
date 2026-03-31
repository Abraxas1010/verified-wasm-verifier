import HeytingLean.PTS.BaseExtension.Main

namespace HeytingLean.PTS.BaseExtension

inductive SearchMode where
  | intuitionistic
  | classicalHorn
  deriving DecidableEq, Repr

def neg (φ : IPL) : IPL :=
  .imp φ .bot

def gmtEmbed : IPL → IPL
  | .atom a => neg (neg (.atom a))
  | .bot => .bot
  | .conj φ ψ => .conj (gmtEmbed φ) (gmtEmbed ψ)
  | .disj φ ψ => neg (neg (.disj (gmtEmbed φ) (gmtEmbed ψ)))
  | .imp φ ψ => .imp (gmtEmbed φ) (gmtEmbed ψ)

def keepHorn : Definite → Bool
  | .absurd => true
  | .atom _ => true
  | .imp g _ =>
      match g with
      | .atom _ => true
      | _ => false
  | .conj d₁ d₂ => keepHorn d₁ && keepHorn d₂
  | .all d => keepHorn d

def hornProjection (P : Program) : Program :=
  P.filter keepHorn

def searchWithMode (mode : SearchMode) (fuel : Nat) (P : Program) (φ : IPL) : Bool :=
  match mode with
  | .intuitionistic => search fuel P (encode φ)
  | .classicalHorn =>
      let projected := hornProjection P
      let direct := search fuel projected (encode φ)
      if direct then true else search fuel projected (encode (gmtEmbed φ))

example : searchWithMode .intuitionistic 5 [] (identityFormula ⟨0⟩) = true := by
  native_decide

example : searchWithMode .classicalHorn 5 [] (identityFormula ⟨0⟩) = true := by
  native_decide

end HeytingLean.PTS.BaseExtension
