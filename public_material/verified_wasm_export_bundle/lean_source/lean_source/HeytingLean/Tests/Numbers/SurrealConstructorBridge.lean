import HeytingLean.Numbers.Surreal.Experimental.ConstructorBridge

namespace HeytingLean
namespace Tests
namespace Numbers

open HeytingLean.Constructor
open HeytingLean.Numbers.Surreal
open HeytingLean.Numbers.Surreal.Experimental
open HeytingLean.Constructor.SurrealAdapter

example : networkRegular canonicalAtom :=
  canonicalAtom_regular

example : Constructor.possible Rcl (networkDenote canonicalAtom) :=
  canonicalAtom_composes_possible

end Numbers
end Tests
end HeytingLean
