import HeytingLean.PDE.Symbolic.Expr
import Lean.Data.Json

namespace HeytingLean.PDE.Symbolic

open Lean (Json)

private def renderReal (value : RealLiteral) : String :=
  value.rendered

/-- Deserialization currently accepts integer renderings only.
Lean-internal `Coe ℝ RealLiteral` values keep the default `"real"` marker and
are therefore intentionally not JSON round-trip safe. -/
private def parseRenderedReal? (text : String) : Option RealLiteral := do
  let value ← text.toInt?
  some { value := (value : ℝ), rendered := text }

mutual

private def scalarExprToJson : ScalarExpr → Json
  | .atom name => Json.mkObj [("tag", Json.str "atom"), ("name", Json.str name)]
  | .real value => Json.mkObj [("tag", Json.str "real"), ("value", Json.str (renderReal value))]
  | .add lhs rhs =>
      Json.mkObj [("tag", Json.str "add"), ("lhs", scalarExprToJson lhs), ("rhs", scalarExprToJson rhs)]
  | .mul lhs rhs =>
      Json.mkObj [("tag", Json.str "mul"), ("lhs", scalarExprToJson lhs), ("rhs", scalarExprToJson rhs)]
  | .div lhs rhs =>
      Json.mkObj [("tag", Json.str "div"), ("lhs", scalarExprToJson lhs), ("rhs", scalarExprToJson rhs)]
  | .neg expr => Json.mkObj [("tag", Json.str "neg"), ("arg", scalarExprToJson expr)]
  | .sqrt expr => Json.mkObj [("tag", Json.str "sqrt"), ("arg", scalarExprToJson expr)]
  | .expI phase => Json.mkObj [("tag", Json.str "expI"), ("arg", scalarExprToJson phase)]
  | .dt expr => Json.mkObj [("tag", Json.str "dt"), ("arg", scalarExprToJson expr)]
  | .dtt expr => Json.mkObj [("tag", Json.str "dtt"), ("arg", scalarExprToJson expr)]
  | .laplacian expr => Json.mkObj [("tag", Json.str "laplacian"), ("arg", scalarExprToJson expr)]
  | .biharmonic expr => Json.mkObj [("tag", Json.str "biharmonic"), ("arg", scalarExprToJson expr)]
  | .divergence expr => Json.mkObj [("tag", Json.str "divergence"), ("arg", vectorExprToJson expr)]
  | .inner lhs rhs =>
      Json.mkObj [("tag", Json.str "inner"), ("lhs", vectorExprToJson lhs), ("rhs", vectorExprToJson rhs)]

private def vectorExprToJson : VectorExpr → Json
  | .atom name => Json.mkObj [("tag", Json.str "atom"), ("name", Json.str name)]
  | .zero => Json.mkObj [("tag", Json.str "zero")]
  | .add lhs rhs =>
      Json.mkObj [("tag", Json.str "add"), ("lhs", vectorExprToJson lhs), ("rhs", vectorExprToJson rhs)]
  | .scale coeff expr =>
      Json.mkObj [("tag", Json.str "scale"), ("coeff", scalarExprToJson coeff), ("arg", vectorExprToJson expr)]
  | .grad expr => Json.mkObj [("tag", Json.str "grad"), ("arg", scalarExprToJson expr)]
  | .dt expr => Json.mkObj [("tag", Json.str "dt"), ("arg", vectorExprToJson expr)]
  | .convective velocity transport =>
      Json.mkObj
        [ ("tag", Json.str "convective")
        , ("velocity", vectorExprToJson velocity)
        , ("transport", vectorExprToJson transport)
        ]
  | .neg expr => Json.mkObj [("tag", Json.str "neg"), ("arg", vectorExprToJson expr)]

end

mutual

private def scalarExprToSMTLIB : ScalarExpr → String
  | .atom name => name
  | .real value => renderReal value
  | .add lhs rhs => "(+ " ++ scalarExprToSMTLIB lhs ++ " " ++ scalarExprToSMTLIB rhs ++ ")"
  | .mul lhs rhs => "(* " ++ scalarExprToSMTLIB lhs ++ " " ++ scalarExprToSMTLIB rhs ++ ")"
  | .div lhs rhs => "(/ " ++ scalarExprToSMTLIB lhs ++ " " ++ scalarExprToSMTLIB rhs ++ ")"
  | .neg expr => "(- " ++ scalarExprToSMTLIB expr ++ ")"
  | .sqrt expr => "(sqrt " ++ scalarExprToSMTLIB expr ++ ")"
  | .expI phase => "(expI " ++ scalarExprToSMTLIB phase ++ ")"
  | .dt expr => "(dt " ++ scalarExprToSMTLIB expr ++ ")"
  | .dtt expr => "(dtt " ++ scalarExprToSMTLIB expr ++ ")"
  | .laplacian expr => "(laplacian " ++ scalarExprToSMTLIB expr ++ ")"
  | .biharmonic expr => "(biharmonic " ++ scalarExprToSMTLIB expr ++ ")"
  | .divergence expr => "(divergence " ++ vectorExprToSMTLIB expr ++ ")"
  | .inner lhs rhs => "(inner " ++ vectorExprToSMTLIB lhs ++ " " ++ vectorExprToSMTLIB rhs ++ ")"

private def vectorExprToSMTLIB : VectorExpr → String
  | .atom name => name
  | .zero => "vzero"
  | .add lhs rhs => "(vadd " ++ vectorExprToSMTLIB lhs ++ " " ++ vectorExprToSMTLIB rhs ++ ")"
  | .scale coeff expr => "(scale " ++ scalarExprToSMTLIB coeff ++ " " ++ vectorExprToSMTLIB expr ++ ")"
  | .grad expr => "(grad " ++ scalarExprToSMTLIB expr ++ ")"
  | .dt expr => "(vdt " ++ vectorExprToSMTLIB expr ++ ")"
  | .convective velocity transport =>
      "(convective " ++ vectorExprToSMTLIB velocity ++ " " ++ vectorExprToSMTLIB transport ++ ")"
  | .neg expr => "(vneg " ++ vectorExprToSMTLIB expr ++ ")"

end

mutual

private def scalarExprToLaTeX : ScalarExpr → String
  | .atom name => name
  | .real value => renderReal value
  | .add lhs rhs => scalarExprToLaTeX lhs ++ " + " ++ scalarExprToLaTeX rhs
  | .mul lhs rhs => scalarExprToLaTeX lhs ++ " \\cdot " ++ scalarExprToLaTeX rhs
  | .div lhs rhs => "\\frac{" ++ scalarExprToLaTeX lhs ++ "}{" ++ scalarExprToLaTeX rhs ++ "}"
  | .neg expr => "-(" ++ scalarExprToLaTeX expr ++ ")"
  | .sqrt expr => "\\sqrt{" ++ scalarExprToLaTeX expr ++ "}"
  | .expI phase => "e^{i(" ++ scalarExprToLaTeX phase ++ ")}"
  | .dt expr => "\\partial_t " ++ scalarExprToLaTeX expr
  | .dtt expr => "\\partial_t^2 " ++ scalarExprToLaTeX expr
  | .laplacian expr => "\\nabla^2 " ++ scalarExprToLaTeX expr
  | .biharmonic expr => "\\nabla^4 " ++ scalarExprToLaTeX expr
  | .divergence expr => "\\nabla \\cdot " ++ vectorExprToLaTeX expr
  | .inner lhs rhs => "\\langle " ++ vectorExprToLaTeX lhs ++ ", " ++ vectorExprToLaTeX rhs ++ " \\rangle"

private def vectorExprToLaTeX : VectorExpr → String
  | .atom name => "\\vec{" ++ name ++ "}"
  | .zero => "\\vec{0}"
  | .add lhs rhs => vectorExprToLaTeX lhs ++ " + " ++ vectorExprToLaTeX rhs
  | .scale coeff expr => scalarExprToLaTeX coeff ++ " " ++ vectorExprToLaTeX expr
  | .grad expr => "\\nabla " ++ scalarExprToLaTeX expr
  | .dt expr => "\\partial_t " ++ vectorExprToLaTeX expr
  | .convective velocity transport =>
      "(" ++ vectorExprToLaTeX velocity ++ " \\cdot \\nabla) " ++ vectorExprToLaTeX transport
  | .neg expr => "-(" ++ vectorExprToLaTeX expr ++ ")"

end

mutual

private def scalarExprFromJsonFuel : Nat → Json → Option ScalarExpr
  | 0, _ => none
  | fuel + 1, json =>
      match json.getObj? with
      | .ok obj =>
          match obj.get? "tag" with
          | some (Json.str "atom") =>
              match obj.get? "name" with
              | some (Json.str name) => some (.atom name)
              | _ => none
          | some (Json.str "real") =>
              match obj.get? "value" with
              | some (Json.str value) => do
                  let parsed ← parseRenderedReal? value
                  some (.real parsed)
              | _ => none
          | some (Json.str "add") =>
              do
                let lhsJson ← obj.get? "lhs"
                let rhsJson ← obj.get? "rhs"
                let lhs ← scalarExprFromJsonFuel fuel lhsJson
                let rhs ← scalarExprFromJsonFuel fuel rhsJson
                pure (.add lhs rhs)
          | some (Json.str "mul") =>
              do
                let lhsJson ← obj.get? "lhs"
                let rhsJson ← obj.get? "rhs"
                let lhs ← scalarExprFromJsonFuel fuel lhsJson
                let rhs ← scalarExprFromJsonFuel fuel rhsJson
                pure (.mul lhs rhs)
          | some (Json.str "div") =>
              do
                let lhsJson ← obj.get? "lhs"
                let rhsJson ← obj.get? "rhs"
                let lhs ← scalarExprFromJsonFuel fuel lhsJson
                let rhs ← scalarExprFromJsonFuel fuel rhsJson
                pure (.div lhs rhs)
          | some (Json.str "neg") =>
              do
                let argJson ← obj.get? "arg"
                let arg ← scalarExprFromJsonFuel fuel argJson
                pure (.neg arg)
          | some (Json.str "sqrt") =>
              do
                let argJson ← obj.get? "arg"
                let arg ← scalarExprFromJsonFuel fuel argJson
                pure (.sqrt arg)
          | some (Json.str "expI") =>
              do
                let argJson ← obj.get? "arg"
                let arg ← scalarExprFromJsonFuel fuel argJson
                pure (.expI arg)
          | some (Json.str "dt") =>
              do
                let argJson ← obj.get? "arg"
                let arg ← scalarExprFromJsonFuel fuel argJson
                pure (.dt arg)
          | some (Json.str "dtt") =>
              do
                let argJson ← obj.get? "arg"
                let arg ← scalarExprFromJsonFuel fuel argJson
                pure (.dtt arg)
          | some (Json.str "laplacian") =>
              do
                let argJson ← obj.get? "arg"
                let arg ← scalarExprFromJsonFuel fuel argJson
                pure (.laplacian arg)
          | some (Json.str "biharmonic") =>
              do
                let argJson ← obj.get? "arg"
                let arg ← scalarExprFromJsonFuel fuel argJson
                pure (.biharmonic arg)
          | some (Json.str "divergence") =>
              do
                let argJson ← obj.get? "arg"
                let arg ← vectorExprFromJsonFuel fuel argJson
                pure (.divergence arg)
          | some (Json.str "inner") =>
              do
                let lhsJson ← obj.get? "lhs"
                let rhsJson ← obj.get? "rhs"
                let lhs ← vectorExprFromJsonFuel fuel lhsJson
                let rhs ← vectorExprFromJsonFuel fuel rhsJson
                pure (.inner lhs rhs)
          | _ => none
      | .error _ => none

private def vectorExprFromJsonFuel : Nat → Json → Option VectorExpr
  | 0, _ => none
  | fuel + 1, json =>
      match json.getObj? with
      | .ok obj =>
          match obj.get? "tag" with
          | some (Json.str "atom") =>
              match obj.get? "name" with
              | some (Json.str name) => some (.atom name)
              | _ => none
          | some (Json.str "zero") => some .zero
          | some (Json.str "add") =>
              do
                let lhsJson ← obj.get? "lhs"
                let rhsJson ← obj.get? "rhs"
                let lhs ← vectorExprFromJsonFuel fuel lhsJson
                let rhs ← vectorExprFromJsonFuel fuel rhsJson
                pure (.add lhs rhs)
          | some (Json.str "scale") =>
              do
                let coeffJson ← obj.get? "coeff"
                let argJson ← obj.get? "arg"
                let coeff ← scalarExprFromJsonFuel fuel coeffJson
                let arg ← vectorExprFromJsonFuel fuel argJson
                pure (.scale coeff arg)
          | some (Json.str "grad") =>
              do
                let argJson ← obj.get? "arg"
                let arg ← scalarExprFromJsonFuel fuel argJson
                pure (.grad arg)
          | some (Json.str "dt") =>
              do
                let argJson ← obj.get? "arg"
                let arg ← vectorExprFromJsonFuel fuel argJson
                pure (.dt arg)
          | some (Json.str "convective") =>
              do
                let velJson ← obj.get? "velocity"
                let trJson ← obj.get? "transport"
                let velocity ← vectorExprFromJsonFuel fuel velJson
                let transport ← vectorExprFromJsonFuel fuel trJson
                pure (.convective velocity transport)
          | some (Json.str "neg") =>
              do
                let argJson ← obj.get? "arg"
                let arg ← vectorExprFromJsonFuel fuel argJson
                pure (.neg arg)
          | _ => none
      | .error _ => none

end

namespace ScalarExpr

def toJson (expr : ScalarExpr) : Json :=
  scalarExprToJson expr

def fromJson? (json : Json) : Option ScalarExpr :=
  scalarExprFromJsonFuel 256 json

def toSMTLIB (expr : ScalarExpr) : String :=
  scalarExprToSMTLIB expr

def toLaTeX (expr : ScalarExpr) : String :=
  scalarExprToLaTeX expr

end ScalarExpr

namespace VectorExpr

def toJson (expr : VectorExpr) : Json :=
  vectorExprToJson expr

def fromJson? (json : Json) : Option VectorExpr :=
  vectorExprFromJsonFuel 256 json

def toSMTLIB (expr : VectorExpr) : String :=
  vectorExprToSMTLIB expr

def toLaTeX (expr : VectorExpr) : String :=
  vectorExprToLaTeX expr

end VectorExpr

namespace ScalarEquation

def toJson (eq : ScalarEquation) : Json :=
  Json.mkObj [("lhs", scalarExprToJson eq.lhs), ("rhs", scalarExprToJson eq.rhs)]

def toSMTLIB (eq : ScalarEquation) : String :=
  "(assert (= " ++ scalarExprToSMTLIB eq.lhs ++ " " ++ scalarExprToSMTLIB eq.rhs ++ "))"

def toLaTeX (eq : ScalarEquation) : String :=
  scalarExprToLaTeX eq.lhs ++ " = " ++ scalarExprToLaTeX eq.rhs

end ScalarEquation

namespace VectorEquation

def toJson (eq : VectorEquation) : Json :=
  Json.mkObj [("lhs", vectorExprToJson eq.lhs), ("rhs", vectorExprToJson eq.rhs)]

def toSMTLIB (eq : VectorEquation) : String :=
  "(assert (= " ++ vectorExprToSMTLIB eq.lhs ++ " " ++ vectorExprToSMTLIB eq.rhs ++ "))"

def toLaTeX (eq : VectorEquation) : String :=
  vectorExprToLaTeX eq.lhs ++ " = " ++ vectorExprToLaTeX eq.rhs

end VectorEquation

namespace CoupledSystem

def toJson (sys : CoupledSystem) : Json :=
  Json.mkObj
    [ ("scalarEquations", Json.arr (sys.scalarEquations.map ScalarEquation.toJson |>.toArray))
    , ("vectorEquations", Json.arr (sys.vectorEquations.map VectorEquation.toJson |>.toArray))
    , ("parameters", Json.arr (sys.parameters.map Json.str |>.toArray))
    , ("assumptions", Json.arr (sys.assumptions.map Json.str |>.toArray))
    ]

def toSMTLIB (sys : CoupledSystem) : String :=
  let scalarLines := sys.scalarEquations.map ScalarEquation.toSMTLIB
  let vectorLines := sys.vectorEquations.map VectorEquation.toSMTLIB
  String.intercalate "\n" ("; PDE symbolic system" :: scalarLines ++ vectorLines)

def toLaTeX (sys : CoupledSystem) : String :=
  let rows :=
    (sys.scalarEquations.map ScalarEquation.toLaTeX) ++
      (sys.vectorEquations.map VectorEquation.toLaTeX)
  "\\begin{align*}\n" ++ String.intercalate " \\\\\n" rows ++ "\n\\end{align*}"

end CoupledSystem

end HeytingLean.PDE.Symbolic
