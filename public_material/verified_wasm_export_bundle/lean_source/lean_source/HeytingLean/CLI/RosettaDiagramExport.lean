import Lean
import Lean.Data.Json
import Std
import HeytingLean.LoF.Rosetta.Diagram
import HeytingLean.LoF.Rosetta.Core

/-
# RosettaDiagramExport CLI

A small CLI that emits a JSON description of canonical Ω_R-style diagrams for
external visualizers. The focus here is on well-typed, schema-stable JSON:

* we expose a tiny diagram AST (`id`, `ofLe`, `comp`, `tensor`) at the JSON level;
* the shapes correspond to constructors of `Rosetta.Diagram`, but the CLI does
  not attempt to parse arbitrary Lean terms from the command line;
* the JSON output is sufficient for external tools to render simple example
  diagrams while remaining aligned with the Ω_R/Rosetta design.

This CLI is intentionally lightweight and free of incomplete semantics.
-/

open Lean Std

/-- A minimal node descriptor for JSON export. -/
structure Node where
  id   : Nat
  name : String

/-- A minimal edge/morphism descriptor for JSON export. -/
structure Edge where
  id    : Nat
  kind  : String
  src   : Nat
  tgt   : Nat
  label : String

def nodeToJson (n : Node) : Json :=
  Json.mkObj
    [ ("id",   Json.num n.id)
      , ("name", Json.str n.name)
    ]

def edgeToJson (e : Edge) : Json :=
  Json.mkObj
    [ ("id",    Json.num e.id)
      , ("kind",  Json.str e.kind)
      , ("src",   Json.num e.src)
      , ("tgt",   Json.num e.tgt)
      , ("label", Json.str e.label)
    ]

/-- Canonical residuation-shaped example diagram at the JSON level.

This captures the idea that a morphism `A ⊗ᵣ B ⟶ C` corresponds to a morphism
`B ⟶ A ⊸ᵣ C`, but we only record the shape, not the actual Lean terms. -/
def residuationExample (lens : String) : Json :=
  let nodes : Array Node :=
    #[ ⟨0, "A"⟩, ⟨1, "B"⟩, ⟨2, "C"⟩ ]
  let edges : Array Edge :=
    #[ ⟨0, "id",        0, 0, "id_A"⟩
     , ⟨1, "primitive", 0, 2, "f : A ⊗ᵣ B ⟶ C"⟩
     , ⟨2, "primitive", 1, 2, "g : B ⟶ A ⊸ᵣ C"⟩
    ]
  Json.mkObj
    [ ("kind",    Json.str "omegaR-diagram")
      , ("lens",  Json.str lens)
      , ("name",  Json.str "residuation")
      , ("nodes", Json.arr <| nodes.map nodeToJson)
      , ("edges", Json.arr <| edges.map edgeToJson)
    ]

/-- Example region-style diagram, corresponding informally to the Heyting
expression `(A ∧ B) ⇒ C` in the Ω_R core. -/
def regionExample : Json :=
  let nodes : Array Node :=
    #[ ⟨0, "A"⟩
     , ⟨1, "B"⟩
     , ⟨2, "C"⟩
     , ⟨3, "A ∧ B"⟩
     , ⟨4, "(A ∧ B) ⇒ C"⟩
     ]
  let edges : Array Edge :=
    #[ ⟨0, "inf-left",   0, 3, "A ≤ A ∧ B"⟩
     , ⟨1, "inf-right",  1, 3, "B ≤ A ∧ B"⟩
     , ⟨2, "himp-left",  3, 4, "A ∧ B ≤ (A ∧ B) ⇒ C"⟩
     , ⟨3, "himp-right", 2, 4, "C ≤ (A ∧ B) ⇒ C"⟩
     ]
  Json.mkObj
    [ ("kind",    Json.str "region-diagram")
      , ("lens",  Json.str "omega")
      , ("name",  Json.str "(A ∧ B) ⇒ C")
      , ("nodes", Json.arr <| nodes.map nodeToJson)
      , ("edges", Json.arr <| edges.map edgeToJson)
    ]

/-- Example graph/flow diagram, corresponding to a simple path
`p ⟶ q ⟶ r` in a graph lens. -/
def graphExample : Json :=
  let nodes : Array Node :=
    #[ ⟨0, "p"⟩, ⟨1, "q"⟩, ⟨2, "r"⟩ ]
  let edges : Array Edge :=
    #[ ⟨0, "edge", 0, 1, "p ⟶ q"⟩
     , ⟨1, "edge", 1, 2, "q ⟶ r"⟩
     ]
  Json.mkObj
    [ ("kind",    Json.str "graph-diagram")
      , ("lens",  Json.str "graph")
      , ("name",  Json.str "p→q→r")
      , ("nodes", Json.arr <| nodes.map nodeToJson)
      , ("edges", Json.arr <| edges.map edgeToJson)
    ]

/-- Example Clifford/operator diagram, corresponding informally to applying a
projector followed by a stage-style Occam operation. -/
def cliffordExample : Json :=
  let nodes : Array Node :=
    #[ ⟨0, "ψ"⟩
     , ⟨1, "P ψ"⟩
     , ⟨2, "Occam(P ψ)"⟩
     ]
  let edges : Array Edge :=
    #[ ⟨0, "project", 0, 1, "project ψ"⟩
     , ⟨1, "stageOccam", 1, 2, "stageOccam (P ψ)"⟩
     ]
  Json.mkObj
    [ ("kind",    Json.str "clifford-diagram")
      , ("lens",  Json.str "clifford")
      , ("name",  Json.str "project⋙Occam")
      , ("nodes", Json.arr <| nodes.map nodeToJson)
      , ("edges", Json.arr <| edges.map edgeToJson)
    ]

/-- Entrypoint: emit a small JSON diagram for Ω_R or a selected visual
calculus.

Usage (modes are by convention and kept intentionally small):

* no arguments / `"omega"` / `"string"`: Ω_R / string-diagram residuation shape;
* `"region"`: region-style Heyting diagram `(A ∧ B) ⇒ C`;
* `"graph"`: graph/flow diagram `p ⟶ q ⟶ r`;
* `"clifford"`: Clifford/operator diagram `project ⋙ stageOccam`. -/
def main (argv : List String) : IO Unit := do
  let mode := match argv with
    | [] => "omega"
    | m :: _ => m
  let j :=
    match mode with
    | "omega" => residuationExample "omega"
    | "string" => residuationExample "omega"
    | "region" => regionExample
    | "graph" => graphExample
    | "clifford" => cliffordExample
    | _ => residuationExample "omega"
  IO.println (toString j)
