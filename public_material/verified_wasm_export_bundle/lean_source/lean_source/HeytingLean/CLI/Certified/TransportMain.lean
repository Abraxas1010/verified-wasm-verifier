import Lean
import Lean.Data.Json
import HeytingLean.CLI.Certified.Json
import HeytingLean.Certified.Library
import HeytingLean.Certified.Transport

open Lean
open HeytingLean.CLI.Certified
open HeytingLean.Certified

def main (args : List String) : IO UInt32 := do
  match (← readInputJson args) with
  | .error e => die e
  | .ok j =>
      let src? := getString? j "src" |>.bind Lens.ofString?
      let dst? := getString? j "dst" |>.bind Lens.ofString?
      let id?  := getString? j "id"
      let cHash? := getString? j "c_hash"
      match src?, dst?, id? with
      | some src, some dst, some id =>
          let lib := CertifiedLibrary.demo
          match lib.find? id with
          | none => die s!"unknown program id: {id}"
          | some p =>
              let ok := decide (src ∈ p.lenses) && decide (dst ∈ p.lenses)
              if !ok then
                return (← die s!"program not transportable between lenses {src} -> {dst}")
              match src, dst with
              | .core, .c
              | .c, .c =>
                  okJson <|
                    Json.mkObj
                      [ ("ok", Json.bool true)
                      , ("src", Json.str (toString src))
                      , ("dst", Json.str (toString dst))
                      , ("artifact", toJson p.artifact)
                      , ("rt1", Json.mkObj [("theorem", Json.str "HeytingLean.Certified.Transport.rt1_artifact_header")])
                      , ("rt2", Json.mkObj [("theorem", Json.str "HeytingLean.Certified.Transport.rt2_cHash_matches")])
                      ]
              | .core, .core =>
                  okJson <|
                    Json.mkObj
                      [ ("ok", Json.bool true)
                      , ("src", Json.str (toString src))
                      , ("dst", Json.str (toString dst))
                      , ("program", toJson p.header)
                      , ("rt1", Json.mkObj [("theorem", Json.str "HeytingLean.Certified.Transport.rt1_artifact_header")])
                      , ("rt2", Json.mkObj [("theorem", Json.str "HeytingLean.Certified.Transport.rt2_cHash_matches")])
                      ]
              | .c, .core =>
                  match cHash? with
                  | none =>
                      die "expected c_hash for src=C,dst=Core"
                  | some ch =>
                      if decide (p.cHash = ch) then
                        okJson <|
                          Json.mkObj
                            [ ("ok", Json.bool true)
                            , ("src", Json.str (toString src))
                            , ("dst", Json.str (toString dst))
                            , ("program", toJson p.header)
                            , ("checked_c_hash", Json.bool true)
                            , ("rt1", Json.mkObj [("theorem", Json.str "HeytingLean.Certified.Transport.rt1_artifact_header")])
                            , ("rt2", Json.mkObj [("theorem", Json.str "HeytingLean.Certified.Transport.rt2_cHash_matches")])
                            ]
                      else
                        die "c_hash mismatch (artifact not recognized by registry)"
      | _, _, _ =>
          die "expected JSON with string keys: src, dst, id"
