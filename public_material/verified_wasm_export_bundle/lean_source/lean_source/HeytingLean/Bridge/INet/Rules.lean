import HeytingLean.Bridge.INet.Basic

/-!
# Bridge.INet.Rules

Staged interaction rules for the direct SKY interaction-net bridge.
These are explicit rule descriptors for the initial implementation phase.
Later phases can refine them into concrete graph rewrites and proofs.
-/

namespace HeytingLean.Bridge.INet

/-- Phase-1 staged interaction rules. -/
inductive InteractionRule where
  | kStage1
  | kStage2
  | sStage1
  | sStage2
  | sStage3
  | yStage
  deriving DecidableEq, Repr, Inhabited

structure RuleSummary where
  rule : InteractionRule
  consumed : List SKYAgent
  produced : List SKYAgent
  duplicatesInput : Bool := false
  erasesArgument : Bool := false
  lazyRecursiveRef : Bool := false
  notes : List String := []
  deriving Repr, Inhabited

def RuleSummary.ofRule : InteractionRule → RuleSummary
  | .kStage1 =>
      { rule := .kStage1
        consumed := [.app, .k]
        produced := [.k1]
        notes := ["APP(REF(K), x) => K1(x)"] }
  | .kStage2 =>
      { rule := .kStage2
        consumed := [.app, .k1]
        produced := [.era]
        erasesArgument := true
        notes := ["APP(K1(x), y) => x with ERA(y)"] }
  | .sStage1 =>
      { rule := .sStage1
        consumed := [.app, .s]
        produced := [.s1]
        notes := ["APP(REF(S), f) => S1(f)"] }
  | .sStage2 =>
      { rule := .sStage2
        consumed := [.app, .s1]
        produced := [.s2]
        notes := ["APP(S1(f), g) => S2(f, g)"] }
  | .sStage3 =>
      { rule := .sStage3
        consumed := [.app, .s2]
        produced := [.app, .app, .app, .dup]
        duplicatesInput := true
        notes := ["APP(S2(f, g), x) => APP(APP(f, x₁), APP(g, x₂)) with DUP(x₁, x₂)"] }
  | .yStage =>
      { rule := .yStage
        consumed := [.app, .y]
        produced := [.app, .y]
        lazyRecursiveRef := true
        notes := ["APP(REF(Y), f) => APP(f, REF(Y)(f))"] }

def InteractionRule.steps : InteractionRule → Nat
  | .kStage1 | .kStage2 | .sStage1 | .sStage2 | .sStage3 | .yStage => 1

def stagedRuleForKinds? : SKYAgent → SKYAgent → Option InteractionRule
  | .app, .k => some .kStage1
  | .app, .k1 => some .kStage2
  | .app, .s => some .sStage1
  | .app, .s1 => some .sStage2
  | .app, .s2 => some .sStage3
  | .app, .y => some .yStage
  | _, _ => none

def INet.activeRuleSummaries (net : INet) : List RuleSummary :=
  net.activePairs.filterMap (fun (lhs, rhs) => do
    let lhsKind ← net.kind? lhs
    let rhsKind ← net.kind? rhs
    let rule ← stagedRuleForKinds? lhsKind rhsKind <|> stagedRuleForKinds? rhsKind lhsKind
    pure (RuleSummary.ofRule rule))

example : stagedRuleForKinds? .app .k = some .kStage1 := rfl
example : stagedRuleForKinds? .app .s2 = some .sStage3 := rfl
example : (RuleSummary.ofRule .yStage).lazyRecursiveRef := by decide

end HeytingLean.Bridge.INet
