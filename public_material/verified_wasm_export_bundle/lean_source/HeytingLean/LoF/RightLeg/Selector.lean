import Mathlib.Order.Nucleus
import HeytingLean.LoF.ComparisonNucleus.Spec
import HeytingLean.LoF.ComparisonNucleus.Soundness

/-!
# LoF Right-Leg nucleus selector (Path A / Path B)

Selector façade that can choose between a default (Option A) nucleus and the
Comparison nucleus (Path B) built from a `CompSpec` bundle. This module does
not alter any certificate/check/ZK plumbing; it only returns a nucleus.
-/

namespace HeytingLean
namespace LoF
namespace RightLeg

open Comparison

universe u v

variable {L : Type u} {Ω : Type v}
variable [CompleteLattice L] [CompleteLattice Ω]

/-- Runtime selector flag for the right-leg nucleus. -/
inductive NucleusOpt
  | optionA
  | comparison
  | auto
  deriving DecidableEq, Inhabited

/-- Select a nucleus from either a fallback (Option A / auto) or a Comparison pack.
    If the `comparison` option is chosen but the pack is missing, we return the
    fallback nucleus without side effects. -/
def select (opt : NucleusOpt)
    (fallback : Nucleus L)
    (pack? : Option (HypPack L Ω)) : Nucleus L :=
  match opt with
  | .optionA   => fallback
  | .auto      => fallback
  | .comparison =>
      match pack? with
      | some P => P.nucleus
      | none   => fallback

end RightLeg
end LoF
end HeytingLean
