import Lean
import HeytingLean.LeanCP.Annotations.Parser

/-!
# LeanCP Annotation Elaboration

Phase 7 lowers the structured annotation DSL directly into the typed annotation
core using Lean macros. This keeps the surface notation checked by Lean while
avoiding brittle runtime parsing or syntax-kind-indexed elaborators.
-/

open Lean Elab Term Meta

namespace HeytingLean.LeanCP

private def mkStringExpr (stx : Syntax) : TermElabM Expr := do
  match stx with
  | Syntax.ident _ _ val _ => pure (toExpr val.toString)
  | _ => elabTermEnsuringType stx (mkConst ``String)

private def mkNatExpr (stx : Syntax) : TermElabM Expr :=
  elabTermEnsuringType stx (mkConst ``Nat)

private def mkListExpr (elemTy : Expr) (xs : List Expr) : TermElabM Expr := do
  let nil := mkAppN (mkConst ``List.nil [Level.zero]) #[elemTy]
  pure <| xs.foldr (fun x acc => mkAppN (mkConst ``List.cons [Level.zero]) #[elemTy, x, acc]) nil

private def asTermSepArray (stx : Syntax) : Syntax.TSepArray `term "," :=
  ⟨stx.getArgs⟩

private def asIdentSepArray (stx : Syntax) : Syntax.TSepArray `ident "," :=
  ⟨stx.getArgs⟩

private def asNumSepArray (stx : Syntax) : Syntax.TSepArray `num "," :=
  ⟨stx.getArgs⟩

macro_rules
  | `(temp $x:ident := $v:term) => do
      let nameStr := quote x.getId.toString
      `(LocalBinding.mk $nameStr $v)

macro_rules
  | `(param $x:ident : $ty:term) => do
      let nameStr := quote x.getId.toString
      `(AnnotatedParam.mk $nameStr $ty)

macro_rules
  | `(assertion%[
        PROP[$ps,*]
        LOCAL[$ls,*]
        SEP[$ss,*]
      ]) => do
      let pureTerms ← ps.getElems.toList.mapM fun p =>
        `(term| SProp.fact $p)
      let spatialTerms ← ss.getElems.toList.mapM fun s =>
        `(term| toSProp $s)
      let pureTerms := pureTerms.toArray
      let spatialTerms := spatialTerms.toArray
      `(Assertion.mk [$[$pureTerms],*] [$[$ls],*] [$[$spatialTerms],*])

macro_rules
  | `(partial_assertion%[
        MODIFIES[$mods,*]
        PROP[$ps,*]
        LOCAL[$ls,*]
        SEP[$ss,*]
      ]) => do
      let modTerms ← mods.getElems.toList.mapM fun m => do
        let nameStr := quote m.getId.toString
        `(term| $nameStr)
      let pureTerms ← ps.getElems.toList.mapM fun p =>
        `(term| SProp.fact $p)
      let spatialTerms ← ss.getElems.toList.mapM fun s =>
        `(term| toSProp $s)
      let modTerms := modTerms.toArray
      let pureTerms := pureTerms.toArray
      let spatialTerms := spatialTerms.toArray
      `(PartialAssertion.mk [$[$modTerms],*] [$[$pureTerms],*] [$[$ls],*] [$[$spatialTerms],*])

elab "func_annotation%[" "name" " := " nm:str ";"
    "params" " := " "[" pms:term,* "]" ";"
    "ret" " := " rty:term ";"
    "requires" " := " pre:term ";"
    "ensures" rv:ident " => " ens:term ";"
    "body" " := " stmt:term
    ";" "modifies" " := " "[" mods:ident,* "]" "]" : term => do
  let nameExpr ← elabTermEnsuringType nm.raw (mkConst ``String)
  let paramExprs ← pms.getElems.toList.mapM (fun p => elabTermEnsuringType p (mkConst ``AnnotatedParam))
  let paramsList ← mkListExpr (mkConst ``AnnotatedParam) paramExprs
  let retExpr ← elabTermEnsuringType rty.raw (mkConst ``CType)
  let requiresExpr ← elabTermEnsuringType pre.raw (mkConst ``Assertion)
  let ensuresTy ← mkArrow (mkConst ``CVal) (mkConst ``Assertion)
  let ensuresStx ← `(term| fun $rv => $ens)
  let ensuresExpr ← elabTermEnsuringType ensuresStx ensuresTy
  let bodyExpr ← elabTermEnsuringType stmt.raw (mkConst ``CStmt)
  let modExprs ← mods.getElems.toList.mapM mkStringExpr
  let modsList ← mkListExpr (mkConst ``String) modExprs
  mkAppM ``FuncAnnotation.mk #[
    nameExpr, paramsList, retExpr, requiresExpr, ensuresExpr, bodyExpr, modsList]

elab "func_annotation%[" "name" " := " nm:str ";"
    "params" " := " "[" pms:term,* "]" ";"
    "ret" " := " rty:term ";"
    "requires" " := " pre:term ";"
    "ensures" rv:ident " => " ens:term ";"
    "body" " := " stmt:term "]" : term => do
  let nameExpr ← elabTermEnsuringType nm.raw (mkConst ``String)
  let paramExprs ← pms.getElems.toList.mapM (fun p => elabTermEnsuringType p (mkConst ``AnnotatedParam))
  let paramsList ← mkListExpr (mkConst ``AnnotatedParam) paramExprs
  let retExpr ← elabTermEnsuringType rty.raw (mkConst ``CType)
  let requiresExpr ← elabTermEnsuringType pre.raw (mkConst ``Assertion)
  let ensuresTy ← mkArrow (mkConst ``CVal) (mkConst ``Assertion)
  let ensuresStx ← `(term| fun $rv => $ens)
  let ensuresExpr ← elabTermEnsuringType ensuresStx ensuresTy
  let bodyExpr ← elabTermEnsuringType stmt.raw (mkConst ``CStmt)
  let modsList ← mkListExpr (mkConst ``String) []
  mkAppM ``FuncAnnotation.mk #[
    nameExpr, paramsList, retExpr, requiresExpr, ensuresExpr, bodyExpr, modsList]

elab "loop_annotation%[" "path" " := " "[" pth:num,* "]" ";"
    "fuel" " := " fuelNum:num ";"
    "invariant" " := " inv:term ";"
    "variant" " := " measure:term "]" : term => do
  let pathExprs ← pth.getElems.toList.mapM mkNatExpr
  let pathList ← mkListExpr (mkConst ``Nat) pathExprs
  let fuelExpr ← mkNatExpr fuelNum.raw
  let invExpr ← elabTermEnsuringType inv.raw (mkConst ``Assertion)
  let variantExpr ← elabTermEnsuringType measure.raw (mkConst ``CExpr)
  let variantOpt ← mkAppM ``Option.some #[variantExpr]
  mkAppM ``LoopAnnotation.mk #[pathList, invExpr, fuelExpr, variantOpt]

elab "loop_annotation%[" "path" " := " "[" pth:num,* "]" ";"
    "fuel" " := " fuelNum:num ";"
    "invariant" " := " inv:term "]" : term => do
  let pathExprs ← pth.getElems.toList.mapM mkNatExpr
  let pathList ← mkListExpr (mkConst ``Nat) pathExprs
  let fuelExpr ← mkNatExpr fuelNum.raw
  let invExpr ← elabTermEnsuringType inv.raw (mkConst ``Assertion)
  let variantOpt ← mkAppM ``Option.none #[mkConst ``CExpr]
  mkAppM ``LoopAnnotation.mk #[pathList, invExpr, fuelExpr, variantOpt]

end HeytingLean.LeanCP
