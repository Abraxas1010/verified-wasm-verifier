import Mathlib.Order.Heyting.Basic

namespace HeytingLean.Bridge.Framework

/-- Trust levels for translated artifacts -/
inductive TrustLevel where
  | kernel
  | verified
  | translated
  | preliminary
  deriving Repr, DecidableEq, Inhabited

/-- Provenance tracking for translated terms -/
structure Provenance where
  sourceSystem : String
  sourceRef : String
  trustLevel : TrustLevel
  translator : String
  timestamp : String
  deriving Repr, Inhabited

/-- Errors that can occur during translation -/
inductive TranslationError where
  | parseError (msg : String)
  | typeError (msg : String)
  | unsupported (feature : String)
  | trustBoundary (msg : String)
  deriving Repr

/-- The translation monad: carries provenance + error handling -/
abbrev TranslateM := ReaderT Provenance (Except TranslationError)

/-- Run a translation with given provenance -/
def TranslateM.run' {α : Type} (prov : Provenance) (m : TranslateM α) : Except TranslationError α :=
  ReaderT.run m prov

end HeytingLean.Bridge.Framework
