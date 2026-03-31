import Lean
import HeytingLean.LoF.ICCKernel.Lower.Constant
import HeytingLean.LoF.ICCKernel.Raise.Expr

namespace HeytingLean
namespace LoF
namespace ICCKernel
namespace Raise

def raiseReducibilityHints : ReducibilityHints → Lean.ReducibilityHints
  | .opaque => .opaque
  | .abbrev => .abbrev
  | .regular height => .regular ⟨height⟩

def raiseDefinitionSafety : DefinitionSafety → Lean.DefinitionSafety
  | .unsafe => .unsafe
  | .safe => .safe
  | .partial => .partial

def raiseQuotKind : QuotKind → Lean.QuotKind
  | .type => .type
  | .ctor => .ctor
  | .lift => .lift
  | .ind => .ind

def raiseConstHeader (v : ConstantVal) : Except LowerError Lean.ConstantVal := do
  let ty ← raiseTerm v.type
  pure
    { name := raiseName v.name
      levelParams := v.levelParams.map raiseName
      type := ty }

def raiseRecursorRule (r : RecursorRule) : Except LowerError Lean.RecursorRule := do
  let rhs ← raiseTerm r.rhs
  pure
    { ctor := raiseName r.ctor
      nfields := r.nfields
      rhs := rhs }

theorem raiseNameList_lowerNameList : ∀ xs : List Lean.Name,
    List.map (raiseName ∘ Lower.lowerName) xs = xs
  | [] => by
      rfl
  | x :: xs => by
      simp [raiseName_lowerName, raiseNameList_lowerNameList xs]

theorem raiseNameList_map_lowerName (xs : List Lean.Name) :
    List.map raiseName (List.map Lower.lowerName xs) = xs := by
  simpa [Function.comp] using raiseNameList_lowerNameList xs

theorem exceptOk_map_eq {α β ε} (f : α → β) (x : α) :
    f <$> (Except.ok x : Except ε α) = .ok (f x) := by
  rfl

theorem exceptOk_bind_map_eq {α β γ ε} (f : α → β → γ) (x : α) (y : β) :
    (do
      let a ← (Except.ok x : Except ε α)
      f a <$> (Except.ok y : Except ε β)) = .ok (f x y) := by
  rfl

theorem exceptOk_bind_ok_eq {α β ε} (f : α → β) (x : α) :
    (do
      let a ← (Except.ok x : Except ε α)
      Except.ok (f a)) = .ok (f x) := by
  rfl

theorem raiseConstHeader_lowerConstHeader (v : Lean.ConstantVal) :
    raiseConstHeader (Lower.lowerConstHeader v) = .ok v := by
  cases v with
  | mk name levelParams type =>
      simpa [raiseConstHeader, Lower.lowerConstHeader, raiseNameList_lowerNameList,
        raiseNameList_map_lowerName, raiseTerm_lowerExprCore, raiseName_lowerName] using
        (exceptOk_map_eq
          (fun ty =>
            Lean.ConstantVal.mk (raiseName (Lower.lowerName name)) levelParams ty)
          type)

def raiseConstantInfo : ConstantInfo → Except LowerError Lean.ConstantInfo
  | .axiomInfo v => do
      let ty ← raiseTerm v.type
      return .axiomInfo
        { name := raiseName v.name
          levelParams := v.levelParams.map raiseName
          type := ty
          isUnsafe := v.isUnsafe }
  | .defnInfo v => do
      let ty ← raiseTerm v.type
      let val ← raiseTerm v.value
      return .defnInfo
        { name := raiseName v.name
          levelParams := v.levelParams.map raiseName
          type := ty
          value := val
          hints := raiseReducibilityHints v.hints
          safety := raiseDefinitionSafety v.safety
          all := v.all.map raiseName }
  | .thmInfo v => do
      let ty ← raiseTerm v.type
      let val ← raiseTerm v.value
      return .thmInfo
        { name := raiseName v.name
          levelParams := v.levelParams.map raiseName
          type := ty
          value := val
          all := v.all.map raiseName }
  | .opaqueInfo v => do
      let ty ← raiseTerm v.type
      let val ← raiseTerm v.value
      return .opaqueInfo
        { name := raiseName v.name
          levelParams := v.levelParams.map raiseName
          type := ty
          value := val
          isUnsafe := v.isUnsafe
          all := v.all.map raiseName }
  | .quotInfo v => do
      let ty ← raiseTerm v.type
      return .quotInfo
        { name := raiseName v.name
          levelParams := v.levelParams.map raiseName
          type := ty
          kind := raiseQuotKind v.kind }
  | .inductInfo v => do
      let ty ← raiseTerm v.type
      return .inductInfo
        { name := raiseName v.name
          levelParams := v.levelParams.map raiseName
          type := ty
          numParams := v.numParams
          numIndices := v.numIndices
          all := v.all.map raiseName
          ctors := v.ctors.map raiseName
          numNested := v.numNested
          isRec := v.isRec
          isUnsafe := v.isUnsafe
          isReflexive := v.isReflexive }
  | .ctorInfo v => do
      let ty ← raiseTerm v.type
      return .ctorInfo
        { name := raiseName v.name
          levelParams := v.levelParams.map raiseName
          type := ty
          induct := raiseName v.induct
          cidx := v.cidx
          numParams := v.numParams
          numFields := v.numFields
          isUnsafe := v.isUnsafe }
  | .recInfo v => do
      let ty ← raiseTerm v.type
      let rules ← v.rules.mapM raiseRecursorRule
      return .recInfo
        { name := raiseName v.name
          levelParams := v.levelParams.map raiseName
          type := ty
          all := v.all.map raiseName
          numParams := v.numParams
          numIndices := v.numIndices
          numMotives := v.numMotives
          numMinors := v.numMinors
          rules := rules
          k := v.k
          isUnsafe := v.isUnsafe }

theorem raiseReducibilityHints_lowerReducibilityHints (h : Lean.ReducibilityHints) :
    raiseReducibilityHints (Lower.lowerReducibilityHints h) = h := by
  cases h <;> simp [Lower.lowerReducibilityHints, raiseReducibilityHints]

theorem raiseDefinitionSafety_lowerDefinitionSafety (s : Lean.DefinitionSafety) :
    raiseDefinitionSafety (Lower.lowerDefinitionSafety s) = s := by
  cases s <;> rfl

theorem raiseQuotKind_lowerQuotKind (k : Lean.QuotKind) :
    raiseQuotKind (Lower.lowerQuotKind k) = k := by
  cases k <;> rfl

theorem raiseRecursorRule_lowerRecursorRule (r : Lean.RecursorRule) :
    raiseRecursorRule (Lower.lowerRecursorRule r) = .ok r := by
  cases r with
  | mk ctor nfields rhs =>
      simpa [Lower.lowerRecursorRule, raiseRecursorRule, raiseTerm_lowerExprCore, raiseName_lowerName] using
        (exceptOk_map_eq
          (fun rhs => Lean.RecursorRule.mk (raiseName (Lower.lowerName ctor)) nfields rhs)
          rhs)

theorem raiseRecursorRuleList_lowerRecursorRuleList : ∀ xs : List Lean.RecursorRule,
    List.mapM (raiseRecursorRule ∘ Lower.lowerRecursorRule) xs = .ok xs
  | [] => by
      rfl
  | x :: xs => by
      simp [raiseRecursorRule_lowerRecursorRule, raiseRecursorRuleList_lowerRecursorRuleList xs]
      simpa using exceptOk_bind_map_eq List.cons x xs

theorem raiseConstantInfo_lowerConstantInfoCore (c : Lean.ConstantInfo) :
    raiseConstantInfo (Lower.lowerConstantInfoCore c) = .ok c := by
  cases c with
  | axiomInfo v =>
      cases v with
      | mk toConstantVal isUnsafe =>
          cases toConstantVal with
          | mk name levelParams type =>
              simpa [Lower.lowerConstantInfoCore, raiseConstantInfo, raiseNameList_lowerNameList,
                raiseNameList_map_lowerName, raiseTerm_lowerExprCore, raiseName_lowerName,
                Lower.lowerConstHeader] using
                (exceptOk_map_eq
                  (fun ty =>
                    Lean.ConstantInfo.axiomInfo
                      { name := raiseName (Lower.lowerConstHeader { name := name, levelParams := levelParams, type := type }).name
                        levelParams := List.map raiseName (Lower.lowerConstHeader { name := name, levelParams := levelParams, type := type }).levelParams
                        type := ty
                        isUnsafe := isUnsafe })
                  type)
  | defnInfo v =>
      cases v with
      | mk toConstantVal value hints safety all =>
          cases toConstantVal with
          | mk name levelParams type =>
              simpa [Lower.lowerConstantInfoCore, raiseConstantInfo, raiseNameList_lowerNameList,
                raiseNameList_map_lowerName,
                raiseTerm_lowerExprCore, raiseReducibilityHints_lowerReducibilityHints,
                raiseDefinitionSafety_lowerDefinitionSafety, raiseName_lowerName,
                Lower.lowerConstHeader] using
                (exceptOk_bind_map_eq
                  (fun ty val =>
                    Lean.ConstantInfo.defnInfo
                      { name := raiseName (Lower.lowerConstHeader { name := name, levelParams := levelParams, type := type }).name
                        levelParams := List.map raiseName (Lower.lowerConstHeader { name := name, levelParams := levelParams, type := type }).levelParams
                        type := ty
                        value := val
                        hints := hints
                        safety := safety
                        all := all })
                  type value)
  | thmInfo v =>
      cases v with
      | mk toConstantVal value all =>
          cases toConstantVal with
          | mk name levelParams type =>
              simpa [Lower.lowerConstantInfoCore, raiseConstantInfo, raiseNameList_lowerNameList,
                raiseNameList_map_lowerName, raiseTerm_lowerExprCore, raiseName_lowerName,
                Lower.lowerConstHeader] using
                (exceptOk_bind_map_eq
                  (fun ty val =>
                    Lean.ConstantInfo.thmInfo
                      { name := raiseName (Lower.lowerConstHeader { name := name, levelParams := levelParams, type := type }).name
                        levelParams := List.map raiseName (Lower.lowerConstHeader { name := name, levelParams := levelParams, type := type }).levelParams
                        type := ty
                        value := val
                        all := all })
                  type value)
  | opaqueInfo v =>
      cases v with
      | mk toConstantVal value isUnsafe all =>
          cases toConstantVal with
          | mk name levelParams type =>
              simpa [Lower.lowerConstantInfoCore, raiseConstantInfo, raiseNameList_lowerNameList,
                raiseNameList_map_lowerName, raiseTerm_lowerExprCore, raiseName_lowerName,
                Lower.lowerConstHeader] using
                (exceptOk_bind_map_eq
                  (fun ty val =>
                    Lean.ConstantInfo.opaqueInfo
                      { name := raiseName (Lower.lowerConstHeader { name := name, levelParams := levelParams, type := type }).name
                        levelParams := List.map raiseName (Lower.lowerConstHeader { name := name, levelParams := levelParams, type := type }).levelParams
                        type := ty
                        value := val
                        isUnsafe := isUnsafe
                        all := all })
                  type value)
  | quotInfo v =>
      cases v with
      | mk toConstantVal kind =>
          cases toConstantVal with
          | mk name levelParams type =>
              simpa [Lower.lowerConstantInfoCore, raiseConstantInfo, raiseTerm_lowerExprCore,
                raiseNameList_lowerNameList, raiseNameList_map_lowerName, raiseQuotKind_lowerQuotKind,
                raiseName_lowerName, Lower.lowerConstHeader] using
                (exceptOk_map_eq
                  (fun ty =>
                    Lean.ConstantInfo.quotInfo
                      { name := raiseName (Lower.lowerConstHeader { name := name, levelParams := levelParams, type := type }).name
                        levelParams := List.map raiseName (Lower.lowerConstHeader { name := name, levelParams := levelParams, type := type }).levelParams
                        type := ty
                        kind := kind })
                  type)
  | inductInfo v =>
      cases v with
      | mk toConstantVal numParams numIndices all ctors numNested isRec isUnsafe isReflexive =>
          cases toConstantVal with
          | mk name levelParams type =>
              simpa [Lower.lowerConstantInfoCore, raiseConstantInfo, raiseNameList_lowerNameList,
                raiseNameList_map_lowerName, raiseTerm_lowerExprCore, raiseName_lowerName,
                Lower.lowerConstHeader] using
                (exceptOk_map_eq
                  (fun ty =>
                    Lean.ConstantInfo.inductInfo
                      { name := raiseName (Lower.lowerConstHeader { name := name, levelParams := levelParams, type := type }).name
                        levelParams := List.map raiseName (Lower.lowerConstHeader { name := name, levelParams := levelParams, type := type }).levelParams
                        type := ty
                        numParams := numParams
                        numIndices := numIndices
                        all := all
                        ctors := ctors
                        numNested := numNested
                        isRec := isRec
                        isUnsafe := isUnsafe
                        isReflexive := isReflexive })
                  type)
  | ctorInfo v =>
      cases v with
      | mk toConstantVal induct cidx numParams numFields isUnsafe =>
          cases toConstantVal with
          | mk name levelParams type =>
              simpa [Lower.lowerConstantInfoCore, raiseConstantInfo, raiseName_lowerName,
                raiseNameList_lowerNameList, raiseNameList_map_lowerName, raiseTerm_lowerExprCore,
                Lower.lowerConstHeader] using
                (exceptOk_map_eq
                  (fun ty =>
                    Lean.ConstantInfo.ctorInfo
                      { name := raiseName (Lower.lowerConstHeader { name := name, levelParams := levelParams, type := type }).name
                        levelParams := List.map raiseName (Lower.lowerConstHeader { name := name, levelParams := levelParams, type := type }).levelParams
                        type := ty
                        induct := induct
                        cidx := cidx
                        numParams := numParams
                        numFields := numFields
                        isUnsafe := isUnsafe })
                  type)
  | recInfo v =>
      cases v with
      | mk toConstantVal all numParams numIndices numMotives numMinors rules k isUnsafe =>
          cases toConstantVal with
          | mk name levelParams type =>
              simpa [Lower.lowerConstantInfoCore, raiseConstantInfo, raiseNameList_lowerNameList,
                raiseNameList_map_lowerName, raiseTerm_lowerExprCore,
                raiseRecursorRuleList_lowerRecursorRuleList, raiseName_lowerName,
                Lower.lowerConstHeader] using
                (exceptOk_bind_map_eq
                  (fun ty rules =>
                    Lean.ConstantInfo.recInfo
                      { name := raiseName (Lower.lowerConstHeader { name := name, levelParams := levelParams, type := type }).name
                        levelParams := List.map raiseName (Lower.lowerConstHeader { name := name, levelParams := levelParams, type := type }).levelParams
                        type := ty
                        all := all
                        numParams := numParams
                        numIndices := numIndices
                        numMotives := numMotives
                        numMinors := numMinors
                        rules := rules
                        k := k
                        isUnsafe := isUnsafe })
                  type rules)

end Raise
end ICCKernel
end LoF
end HeytingLean
