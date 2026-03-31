import HeytingLean.Chem.Materials.SLICES.QuotientGraph
import HeytingLean.Chem.PeriodicTable.Lookup
import Std

/-!
# SLICES: syntax helpers (Phase 2)

This file provides lightweight helpers for tokenizing and parsing the SLICES text format.

We intentionally keep this layer simple and totality-aware (returning `Except String ...` on
failure). The canonicalization layer (Phase 3) sits above the codec.
-/

namespace HeytingLean.Chem.Materials.SLICES

open HeytingLean.Chem.PeriodicTable

def tokenize (s : String) : List String :=
  (s.split Char.isWhitespace).filter (fun t => t != "")

def isNatToken (t : String) : Bool :=
  match t.toNat? with
  | some _ => true
  | none => false

structure RawEdge where
  u : Nat
  v : Nat
  t : TranslationVec
deriving Repr, DecidableEq

structure Parsed where
  atoms : List Element
  edges : List RawEdge
deriving Repr

def parseAtoms (atomTokens : List String) : Except String (List Element) := do
  let mut out : List Element := []
  for t in atomTokens do
    match ofSymbol? t with
    | some e => out := out.concat e
    | none => throw s!"Unknown element symbol: {t}"
  return out

def parseRawEdges (edgeTokens : List String) : Except String (List RawEdge) := do
  if edgeTokens.length % 5 != 0 then
    throw s!"Edge token count must be a multiple of 5 (u v x y z). Got {edgeTokens.length}."

  let mut out : List RawEdge := []
  let mut i : Nat := 0
  while i < edgeTokens.length do
    let uTok := edgeTokens[i]!
    let vTok := edgeTokens[i + 1]!
    let xTok := edgeTokens[i + 2]!
    let yTok := edgeTokens[i + 3]!
    let zTok := edgeTokens[i + 4]!
    let u ←
      match uTok.toNat? with
      | some n => pure n
      | none => throw s!"Expected Nat for u; got: {uTok}"
    let v ←
      match vTok.toNat? with
      | some n => pure n
      | none => throw s!"Expected Nat for v; got: {vTok}"
    let x ←
      match xTok.toInt? with
      | some z => pure z
      | none => throw s!"Expected Int for x; got: {xTok}"
    let y ←
      match yTok.toInt? with
      | some z => pure z
      | none => throw s!"Expected Int for y; got: {yTok}"
    let z ←
      match zTok.toInt? with
      | some z' => pure z'
      | none => throw s!"Expected Int for z; got: {zTok}"
    out := out.concat { u := u, v := v, t := { x := x, y := y, z := z } }
    i := i + 5
  return out

def parse (s : String) : Except String Parsed := do
  let toks := tokenize s
  let atomToks := toks.takeWhile (fun t => !(isNatToken t))
  let edgeToks := toks.drop atomToks.length
  let atoms ← parseAtoms atomToks
  let edges ← parseRawEdges edgeToks
  return { atoms := atoms, edges := edges }

end HeytingLean.Chem.Materials.SLICES
