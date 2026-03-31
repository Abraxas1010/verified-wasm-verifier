import Lean
import Std
import HeytingLean.Logic.ReflectionProgression

open Std
open Lean
open HeytingLean.Logic

namespace HeytingLean
namespace CLI
namespace OFIProgression

/-! ### Atom universe and formulas -/

inductive Atom
  | alpha | beta | gamma | delta | eps
deriving DecidableEq, Repr

noncomputable instance : Fintype Atom :=
  Fintype.ofList
    [Atom.alpha, Atom.beta, Atom.gamma, Atom.delta, Atom.eps]
    (by
      intro a
      cases a <;> decide)

private def atomName : Atom → String
  | Atom.alpha => "alpha"
  | Atom.beta  => "beta"
  | Atom.gamma => "gamma"
  | Atom.delta => "delta"
  | Atom.eps   => "eps"

open scoped Classical

abbrev Formula := Set Atom

noncomputable instance : DecidableEq Formula := Classical.decEq _

noncomputable def setOfAtoms (xs : List Atom) : Formula := fun a => a ∈ xs

private def parseAtom (s : String) : Option Atom :=
  match s.trim.toLower with
  | "a" | "alpha" => some Atom.alpha
  | "b" | "beta"  => some Atom.beta
  | "g" | "gamma" => some Atom.gamma
  | "d" | "delta" => some Atom.delta
  | "e" | "eps" | "epsilon" => some Atom.eps
  | _ => none

private def parseFormula (raw : String) : Option Formula := do
  let trimmed := raw.trim
  if trimmed = "" then
    none
  else
    let atoms := trimmed.splitOn "+"
    let parsed ← atoms.mapM parseAtom
    if parsed.isEmpty then
      none
    else
      some (setOfAtoms parsed)

private def parseFormulaList (payload : String) : Option (List Formula) := do
  let entries := payload.splitOn ";"
  let trimmed := entries.filter (·.trim ≠ "")
  if trimmed.isEmpty then none else trimmed.mapM parseFormula

noncomputable def formulaToList (f : Formula) : List Atom :=
  (Fintype.elems (α := Atom)).toList.filter fun a => decide (a ∈ f)

noncomputable def encodeFormula (f : Formula) : Json :=
  Json.arr (((formulaToList f).map (Json.str ∘ atomName)).toArray)

noncomputable def encodeGamma (Γ : Finset Formula) : Json :=
  Json.arr (((Γ.val.toList).map encodeFormula).toArray)

/-! ### Strategy description -/

structure GammaStrategy where
  name : String
  select : List (Nucleus Formula) → Nat → Finset Formula

namespace GammaStrategy

noncomputable def static (Γ₀ : Finset Formula) : GammaStrategy :=
  ⟨"static", fun _ _ => Γ₀⟩

noncomputable def incremental [DecidableEq Formula]
    (catalog : List Formula) : GammaStrategy :=
  ⟨"incremental", fun _ n =>
      let takeN := min (n + 1) catalog.length
      (catalog.take takeN).toFinset⟩

noncomputable def unproven [DecidableEq Formula]
    (pool : Finset Formula) : GammaStrategy :=
  ⟨"unproven", fun history _ =>
      match history.getLast? with
      | some curr => pool.filter (fun p => curr (curr p ⇨ p) ≠ ⊤)
      | none => pool⟩

end GammaStrategy

/-! ### Progression builder over `Nat` -/

structure Progression where
  stages : List (Nucleus Formula)   -- stage 0 first
  gammas : List (Finset Formula)    -- gamma for transition i
  deriving Inhabited

noncomputable def buildProgression
    (R₀ : Nucleus Formula) (strategy : GammaStrategy)
    (steps : Nat) : Progression :=
  let rec go : Nat → List (Nucleus Formula) → List (Finset Formula) → Progression
    | 0, stages, gammas => { stages := stages.reverse, gammas := gammas.reverse }
    | Nat.succ _, [], gammas => { stages := [], gammas := gammas.reverse }
    | Nat.succ k, curr :: rest, gammas =>
        let history := (curr :: rest).reverse
        let Γ := strategy.select history k
        let next := HeytingLean.Logic.succStepUniform (α := Formula) curr Γ
        go k (next :: curr :: rest) (Γ :: gammas)
  go steps [R₀] []

private def stageAt? (prog : Progression) (n : Nat) : Option (Nucleus Formula) :=
  prog.stages[n]?

private def gammaAt? (prog : Progression) (n : Nat) : Option (Finset Formula) :=
  prog.gammas[n]?

noncomputable def madeTrue (prog : Progression) (n : Nat) : Option (Finset Formula) := do
  let Γ ← gammaAt? prog n
  let curr ← stageAt? prog n
  let next ← stageAt? prog (n + 1)
  pure <| Γ.filter (fun p => next (curr p ⇨ p) = ⊤)

noncomputable def ofiNat (prog : Progression) (p : Formula) (cutoff : Nat) : Option Nat :=
  let limit := min cutoff (prog.gammas.length)
  let candidates := List.range (limit + 1)
  candidates.find? (fun n =>
    match stageAt? prog n, stageAt? prog (n + 1) with
    | some curr, some next => decide (curr p = next p)
    | _, _ => false)

/-! ### Default catalogs -/

noncomputable def demoCatalog : List Formula :=
  [ setOfAtoms [Atom.alpha]
  , setOfAtoms [Atom.beta]
  , setOfAtoms [Atom.gamma]
  , setOfAtoms [Atom.alpha, Atom.beta]
  , setOfAtoms [Atom.beta, Atom.gamma]
  , setOfAtoms [Atom.delta]
  , setOfAtoms [Atom.eps]
  , setOfAtoms [Atom.alpha, Atom.gamma, Atom.eps] ]

noncomputable def demoPool : Finset Formula :=
  (demoCatalog ++ [setOfAtoms [Atom.alpha, Atom.delta], setOfAtoms [Atom.beta, Atom.eps]]).toFinset
  

/-! ### CLI args -/

structure Args where
  cutoff : Nat := 5
  strategy : String := "incremental"
  gammaPreset : String := "demo"
  gammaList : Option String := none
  emitSchemas : Bool := false
  target : Option String := none
  mode : String := "progression"
  law  : String := "uniform"
  deriving Inhabited

private def parseArgs (xs : List String) : Args :=
  let rec go (st : Args) : List String → Args
    | [] => st
    | "--cutoff" :: v :: rest =>
        match v.toNat? with
        | some n => go { st with cutoff := n } rest
        | none   => go st rest
    | "--strategy" :: v :: rest => go { st with strategy := v } rest
    | "--gamma-preset" :: v :: rest => go { st with gammaPreset := v } rest
    | "--gamma-list" :: v :: rest => go { st with gammaList := some v } rest
    | "--target" :: v :: rest => go { st with target := some v } rest
    | "--emit-schemas" :: rest => go { st with emitSchemas := true } rest
    | "--mode" :: v :: rest => go { st with mode := v } rest
    | "--law" :: v :: rest => go { st with law := v } rest
    | _ :: rest => go st rest
  go ({} : Args) xs

/-! ### Strategy selection -/

noncomputable def assembleStrategy (args : Args) : Except String GammaStrategy :=
  if let some payload := args.gammaList then
    match parseFormulaList payload with
    | some fs => .ok <| GammaStrategy.static fs.toFinset
    | none => .error "unable to parse --gamma-list"
  else
    match args.strategy.trim.toLower with
    | "static" =>
        let base := if args.gammaPreset.trim.toLower = "demo" then demoCatalog.take 3 else demoCatalog
        .ok <| GammaStrategy.static base.toFinset
    | "incremental" => .ok <| GammaStrategy.incremental demoCatalog
    | "unproven"    => .ok <| GammaStrategy.unproven demoPool
    | other => .error s!"unknown strategy '{other}'"

/-! ### Base nucleus and helpers -/

noncomputable def baseFormula : Formula := setOfAtoms [Atom.alpha]

noncomputable def baseNucleus : Nucleus Formula :=
  HeytingLean.Logic.openNucleus (α := Formula) baseFormula

noncomputable def targetFormula (args : Args) : Except String Formula :=
  match args.target with
  | none => .ok (setOfAtoms [Atom.alpha])
  | some s =>
    match parseFormula s with
    | some f => .ok f
    | none => .error "unable to parse --target"

/-! ### JSON assembly -/

noncomputable def stagesJson (prog : Progression) (args : Args) : Json :=
  let indices := List.range prog.gammas.length
  let entries := indices.map fun n =>
    let gammaJson :=
      match gammaAt? prog n with
      | some Γ => encodeGamma Γ
      | none   => Json.arr #[]
    let madeJson :=
      if args.emitSchemas then
        match madeTrue prog n with
        | some Γ => encodeGamma Γ
        | none   => Json.arr #[]
      else Json.arr #[]
    Json.mkObj
      [ ("n", Json.num n)
      , ("gamma", gammaJson)
      , ("madeTrue", madeJson) ]
  Json.arr entries.toArray

noncomputable def ofiJson (prog : Progression) (args : Args) (target : Formula) : Json :=
  let idx? := ofiNat prog target args.cutoff
  Json.mkObj
    [ ("target", encodeFormula target)
    , ("stable", Json.bool idx?.isSome)
    , ("index", match idx? with | some n => Json.num n | none => Json.null)
    , ("kind", Json.str (if idx?.isSome then "successor" else "unknown")) ]

/-! ### Entry point -/

noncomputable def runWithArgs (argv : List String) : IO UInt32 := do
  let args := parseArgs argv
  if args.mode.trim.toLower ≠ "progression" then
    IO.println (Json.mkObj [("error", Json.str "only progression mode supported")]).pretty
    return 1
  if args.law.trim.toLower ≠ "uniform" then
    IO.println (Json.mkObj [("error", Json.str "only uniform law supported")]).pretty
    return 1
  match assembleStrategy args with
  | .error msg =>
    IO.println (Json.mkObj [("error", Json.str msg)]).pretty
    return 1
  | .ok strat =>
    match targetFormula args with
    | .error msg =>
      IO.println (Json.mkObj [("error", Json.str msg)]).pretty
      return 1
    | .ok target =>
      let prog := buildProgression baseNucleus strat args.cutoff
      let payload := Json.mkObj
        [ ("mode", Json.str args.mode)
        , ("law", Json.str args.law)
        , ("strategy", Json.str strat.name)
        , ("cutoff", Json.num args.cutoff)
        , ("stages", stagesJson prog args)
        , ("ofi", ofiJson prog args target) ]
      IO.println payload.pretty
      return 0

end OFIProgression
end CLI
end HeytingLean
