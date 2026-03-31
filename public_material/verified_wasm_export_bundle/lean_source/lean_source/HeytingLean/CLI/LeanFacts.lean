import Lean
import Lean.Data.Json
import HeytingLean.CLI.EnvBootstrap

open Lean

private def countForalls (e : Expr) : Nat :=
  match e with
  | Expr.forallE _ _ b _ => 1 + countForalls b
  | _ => 0

private def headConstName? (e : Expr) : Option Name :=
  let rec head (t : Expr) : Option Name :=
    match t with
    | Expr.forallE _ _ b _ => head b
    | Expr.lam _ _ b _      => head b
    | Expr.letE _ _ _ b _   => head b
    | Expr.app f _          => head f
    | Expr.const n _        => some n
    | _                     => none
  head e

private partial def propShape (e : Expr) (fuel : Nat := 128) : String :=
  if fuel = 0 then "_"
  else
    match e with
    | Expr.forallE _ ty b _ =>
        let d := s!"forall({propShape ty (fuel-1)},{propShape b (fuel-1)})"
        d
    | Expr.lam _ ty b _ => s!"lam({propShape ty (fuel-1)},{propShape b (fuel-1)})"
    | Expr.app f a => s!"app({propShape f (fuel-1)},{propShape a (fuel-1)})"
    | Expr.const n _ => s!"const({n.toString})"
    | Expr.sort _ => "sort"
    | Expr.mvar .. => "_"
    | Expr.fvar .. => "_"
    | Expr.bvar .. => "_"
    | Expr.letE _ ty v b _ => s!"let({propShape ty (fuel-1)},{propShape v (fuel-1)},{propShape b (fuel-1)})"
    | Expr.mdata _ b => propShape b (fuel-1)
    | Expr.proj _ _ b => s!"proj({propShape b (fuel-1)})"
    | _ => "_"

private def collectConsts (e : Expr) : StateM (Std.HashSet Name) Unit := do
  match e with
  | Expr.const n _ => do
      let s ← get
      if !s.contains n then
        set <| s.insert n
  | Expr.app f a => do collectConsts f; collectConsts a
  | Expr.lam _ ty b _ => do collectConsts ty; collectConsts b
  | Expr.forallE _ ty b _ => do collectConsts ty; collectConsts b
  | Expr.letE _ ty v b _ => do collectConsts ty; collectConsts v; collectConsts b
  | Expr.mdata _ b => collectConsts b
  | Expr.proj _ _ b => collectConsts b
  | _ => pure ()

def main (_argv : List String) : IO Unit := do
  HeytingLean.CLI.EnvBootstrap.bootstrapSearchPath

  let env ← importModules #[{module := `Init}, {module := `HeytingLean}] {}
  let mut arr : Array Json := #[]
  for (n, ci) in env.constants.toList do
    if !n.toString.startsWith "HeytingLean." then
      continue
    let kind := match ci with
      | .thmInfo _     => "theorem"
      | .axiomInfo _   => "axiom_decl"
      | .defnInfo _    => "def"
      | .opaqueInfo _  => "opaque"
      | .quotInfo _    => "quot"
      | .inductInfo _  => "inductive"
      | .ctorInfo _    => "ctor"
      | .recInfo _     => "recursor"
    -- Only export facts for theorem/def/lemma‑like things
    let ty := ci.type
    let typePP := toString ty
    let head := (headConstName? ty).getD n
    let fCount := countForalls ty
    let refsList := ((collectConsts ty).run {}).snd.toList
      |>.filter (fun nm => nm.toString.startsWith "HeytingLean.")
      |>.map (fun nm => Json.str nm.toString)
    let refs := refsList.toArray
    let j := Json.mkObj
      [ ("name", Json.str n.toString)
      , ("kind", Json.str kind)
      , ("head", Json.str head.toString)
      , ("typePP", Json.str typePP)
      , ("propShape", Json.str (propShape ty))
      , ("forallCount", Json.num fCount)
      , ("refs", Json.arr refs)
      ]
    arr := arr.push j
  IO.println (toString (Json.arr arr))
