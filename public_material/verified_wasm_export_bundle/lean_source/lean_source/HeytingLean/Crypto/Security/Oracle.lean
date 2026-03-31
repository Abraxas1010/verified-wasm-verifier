namespace HeytingLean
namespace Crypto
namespace Security

/-- Shared adversary/query budget carried by native security surfaces. -/
structure Budget where
  randomOracleQueries : Nat
  decapsulationQueries : Nat
  signingQueries : Nat
  auxiliaryQueries : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Shared oracle surface used by native game and reduction statements. -/
structure OracleModel (Query Response : Type) where
  budget : Budget
  answer : Query → Option Response

end Security
end Crypto
end HeytingLean
