import HeytingLean.CCI.Core

/-!
# Rewrite table (v1)

Frozen RuleId namespace; pure, no-search application.
-/

namespace HeytingLean
namespace CCI

abbrev RuleId := Nat

namespace Rule

/-!
Rewrite-rule identifiers for the CCI IR.

These are intentionally tiny and *syntax-directed* (no search): a certificate
lists rule IDs to replay deterministically.
-/

def doubleNeg : RuleId := 1
def deMorgan_and : RuleId := 2
def deMorgan_or : RuleId := 3
def imp_to_or : RuleId := 4

def name (rid : RuleId) : String :=
  match rid with
  | 1 => "doubleNeg"
  | 2 => "deMorgan_and"
  | 3 => "deMorgan_or"
  | 4 => "imp_to_or"
  | _ => s!"unknown({rid})"

end Rule

def applyById (rid : RuleId) (e : Expr) : Option Expr :=
  match rid, e with
  | 1, .notR (.notR a) =>
      some a
  | 2, .notR (.andR a b) =>
      some (.orR (.notR a) (.notR b))
  | 3, .notR (.orR a b) =>
      some (.andR (.notR a) (.notR b))
  | 4, .impR a b =>
      some (.orR (.notR a) b)
  | _, _ => none

end CCI
end HeytingLean
