import Lean
import Lean.Data.Json
import HeytingLean.Crypto.Form

/-!
JSON codec scaffolding for HeytingLean.Crypto.Form. Provides a general
`toJson` encoder and a small `fromJson3` decoder for arity 3 forms used in
our demo and test vectors.
-/

namespace HeytingLean
namespace Crypto

open Lean

def formToJson {n : Nat} : Form n → Json
  | .top       => Json.mkObj [("tag", Json.str "top")]
  | .bot       => Json.mkObj [("tag", Json.str "bot")]
  | .var i     => Json.mkObj [
      ("tag", Json.str "var"),
      ("idx", Json.str (toString i.val))
    ]
  | .and φ ψ   => Json.mkObj [
      ("tag", Json.str "and"),
      ("lhs", formToJson φ),
      ("rhs", formToJson ψ)
    ]
  | .or φ ψ    => Json.mkObj [
      ("tag", Json.str "or"),
      ("lhs", formToJson φ),
      ("rhs", formToJson ψ)
    ]
  | .imp φ ψ   => Json.mkObj [
      ("tag", Json.str "imp"),
      ("lhs", formToJson φ),
      ("rhs", formToJson ψ)
    ]

namespace Form3

open Lean

-- Very small parser compatible with Docs/Examples/tiny_form.json schema.
private def fromJsonFuel : Nat → Json → Option (Form 3)
  | 0, _ => none
  | fuel + 1, j =>
      match j.getObj? with
      | .error _ => none
      | .ok o =>
        let get? (k : String) : Option Json := o.get? k
        match get? "tag" with
        | some (Json.str "top") => some .top
        | some (Json.str "bot") => some .bot
        | some (Json.str "var") =>
            match get? "idx" with
            | some (Json.str s) =>
                match s.toNat? with
                | some n => if h : n < 3 then some (.var ⟨n, h⟩) else none
                | none => none
            | _ => none
        | some (Json.str "and") =>
            match (get? "lhs", get? "rhs") with
            | (some lhs, some rhs) =>
                match (fromJsonFuel fuel lhs, fromJsonFuel fuel rhs) with
                | (some l, some r) => some (.and l r)
                | _ => none
            | _ => none
        | some (Json.str "or") =>
            match (get? "lhs", get? "rhs") with
            | (some lhs, some rhs) =>
                match (fromJsonFuel fuel lhs, fromJsonFuel fuel rhs) with
                | (some l, some r) => some (.or l r)
                | _ => none
            | _ => none
        | some (Json.str "imp") =>
            match (get? "lhs", get? "rhs") with
            | (some lhs, some rhs) =>
                match (fromJsonFuel fuel lhs, fromJsonFuel fuel rhs) with
                | (some l, some r) => some (.imp l r)
                | _ => none
            | _ => none
        | _ => none

def fromJson (j : Json) : Option (Form 3) :=
  fromJsonFuel 256 j

end Form3

end Crypto
end HeytingLean
