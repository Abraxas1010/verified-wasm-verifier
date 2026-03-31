namespace HeytingLean.HeytingVeil.ModelCheck

structure Config where
  maxDepth : Nat := 64
  maxNodes : Nat := 10000
  deriving Repr, DecidableEq

end HeytingLean.HeytingVeil.ModelCheck
