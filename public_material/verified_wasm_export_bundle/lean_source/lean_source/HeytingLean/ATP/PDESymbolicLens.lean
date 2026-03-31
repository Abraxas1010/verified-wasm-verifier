import HeytingLean.PDE
import HeytingLean.Symbolic

namespace HeytingLean.ATP

open HeytingLean.Symbolic

private def sortTag : SymSort → String
  | .bool => "bool"
  | .int => "int"
  | .real => "real"
  | .bitvec w => s!"bv{w}"
  | .array _ _ => "array"

def symbolicSignature (problem : Problem) : List String :=
  let p := problem.withInferredDecls
  let sortTags := p.declarations.map (fun d => s!"sym:{sortTag d.sort}")
  let relTags := p.constraints.map (fun c =>
    match c.rel with
    | .eq => "rel:eq"
    | .ne => "rel:ne"
    | .le => "rel:le"
    | .lt => "rel:lt"
    | .ge => "rel:ge"
    | .gt => "rel:gt")
  [s!"logic:{p.logic}"] ++ sortTags ++ relTags ++ p.tags

def pdeSignature (spec : HeytingLean.PDE.PDESpec) : List String :=
  let classTag :=
    match spec.pdeClass with
    | .elliptic => "pde:elliptic"
    | .parabolic => "pde:parabolic"
    | .hyperbolic => "pde:hyperbolic"
    | .variational => "pde:variational"
  let dimTag := s!"pde:dim:{spec.dimension}"
  classTag :: dimTag :: spec.tags

def retrievalQuery (spec : HeytingLean.PDE.PDESpec) : String :=
  String.intercalate " " (pdeSignature spec)

end HeytingLean.ATP
