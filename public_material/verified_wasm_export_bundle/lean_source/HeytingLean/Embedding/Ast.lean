import Lean
import Lean.Data.Json

namespace HeytingLean.Embedding

open Lean

inductive AstNode where
  | bvar (idx : Nat)
  | fvar (name : String)
  | const (name : String)
  | lit (value : String)
  | app
  | lam (binder : String)
  | forallE (binder : String)
  | letE (binder : String)
  | proj (struct : String) (idx : Nat)
  | other (tag : String)
  deriving Repr, Inhabited

structure AstTree where
  node : AstNode
  children : Array AstTree
  deriving Repr, Inhabited

def AstTree.countNodes : AstTree → Nat
  | ⟨_, cs⟩ => 1 + cs.foldl (fun acc t => acc + t.countNodes) 0

def AstNode.kind : AstNode → String
  | .bvar _     => "bvar"
  | .fvar _     => "fvar"
  | .const _    => "const"
  | .lit _      => "lit"
  | .app        => "app"
  | .lam _      => "lam"
  | .forallE _  => "forallE"
  | .letE _     => "letE"
  | .proj _ _   => "proj"
  | .other _    => "other"

def AstNode.value? : AstNode → Option String
  | .bvar idx        => some (toString idx)
  | .fvar name       => some name
  | .const name      => some name
  | .lit value       => some value
  | .lam binder      => some binder
  | .forallE binder  => some binder
  | .letE binder     => some binder
  | .proj struct idx => some s!"{struct}#{idx}"
  | .app             => none
  | .other tag       => some tag

def AstNode.toJson (n : AstNode) : Json :=
  match n.value? with
  | none => Json.mkObj [("kind", Json.str n.kind)]
  | some v => Json.mkObj [("kind", Json.str n.kind), ("value", Json.str v)]

partial def AstTree.toJson (t : AstTree) : Json :=
  let base := #[("node", t.node.toJson)]
  if t.children.isEmpty then
    Json.mkObj base.toList
  else
    Json.mkObj (base.push ("children", Json.arr (t.children.map AstTree.toJson))).toList

end HeytingLean.Embedding
