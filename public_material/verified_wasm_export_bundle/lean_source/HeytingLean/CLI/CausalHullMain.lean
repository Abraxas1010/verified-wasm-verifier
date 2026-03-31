import Lean
import Lean.Data.Json
import HeytingLean.CLI.Args

namespace HeytingLean.CLI.CausalHullMain

open Lean

structure EdgeRaw where
  src : String
  tgt : String

structure Args where
  edges : Array EdgeRaw := #[]
  S     : Array String := #[]
deriving Inhabited

private def parseEdge? (raw : String) : Option EdgeRaw := do
  match raw.splitOn "," with
  | [a, b] =>
      let a := a.trim
      let b := b.trim
      if a = "" || b = "" then none else some ⟨a, b⟩
  | _ => none

private def parseSList (raw : String) : Array String :=
  raw.splitOn ","
    |>.map (·.trim)
    |>.filter (· ≠ "")
    |>.toArray

private def parseArgs (argv : List String) : Except String Args :=
  let rec go (st : Args) (xs : List String) : Except String Args :=
    match xs with
    | [] => .ok st
    | "--edge" :: v :: rest =>
        match parseEdge? v with
        | some e => go { st with edges := st.edges.push e } rest
        | none => .error "bad --edge (expected a,b)"
    | "--S" :: v :: rest =>
        let s := parseSList v
        go { st with S := st.S ++ s } rest
    | tok :: rest =>
        if tok.startsWith "--edge=" then
          let payload := tok.drop 7
          match parseEdge? payload with
          | some e => go { st with edges := st.edges.push e } rest
          | none => .error "bad --edge=... (expected a,b)"
        else if tok.startsWith "--S=" then
          let payload := tok.drop 4
          go { st with S := st.S ++ parseSList payload } rest
        else
          go st rest
  go ({} : Args) argv

private def sortDedup (xs : List String) : List String :=
  (xs.mergeSort (le := fun a b => a ≤ b)).eraseDups

private def jNat (n : Nat) : Json :=
  Json.num (JsonNumber.fromNat n)

private def jsonNatArray (xs : Array Nat) : Json :=
  Json.arr (xs.map jNat)

private def jsonEdgeArray (xs : Array (Nat × Nat)) : Json :=
  let items := xs.map (fun (u, v) => Json.arr #[jNat u, jNat v])
  Json.arr items

private def computeHull (nodeCount : Nat) (edges : Array (Nat × Nat)) (S : Array Nat) : Array Nat :=
  Id.run do
    if nodeCount = 0 then
      return #[]
    let mut inHull : Array Bool := Array.replicate nodeCount false
    for s in S do
      if s < nodeCount then
        inHull := inHull.set! s true
    let mut changed := true
    while changed do
      changed := false
      for (u, v) in edges do
        if u < nodeCount then
          if v < nodeCount then
            if inHull[v]! && !inHull[u]! then
              inHull := inHull.set! u true
              changed := true
    let mut out : Array Nat := #[]
    for i in [0:nodeCount] do
      if inHull[i]! then
        out := out.push i
    return out

private def usage : String :=
  String.intercalate "\n"
    [ "causal_hull"
    , ""
    , "Usage:"
    , "  causal_hull --edge A,B --edge B,C --S C"
    , ""
    , "Flags:"
    , "  --edge a,b    Repeatable directed edges a->b"
    , "  --S x,y,z     Target set (comma-separated)"
    ]

def run (argv : List String) : IO Unit := do
  let argv := HeytingLean.CLI.stripLakeArgs argv
  if argv.contains "--help" || argv.contains "-h" then
    IO.println usage
    return

  match parseArgs argv with
  | .error msg =>
      IO.eprintln msg
      IO.Process.exit 1
  | .ok args =>
      let nodeNames :=
        sortDedup <|
          List.flatMap (fun e => [e.src, e.tgt]) args.edges.toList ++
          args.S.toList
      let nodes : Array String := nodeNames.toArray
      let edgesIdx : Array (Nat × Nat) :=
        args.edges.map (fun e =>
          (nodes.findIdx (fun s => s == e.src), nodes.findIdx (fun s => s == e.tgt)))
      let SIdx : Array Nat := args.S.map (fun s => nodes.findIdx (fun t => t == s))
      let hullIdx := computeHull nodes.size edgesIdx SIdx

      let j := Json.mkObj
        [ ("nodes", Json.arr (nodes.map Json.str))
        , ("edges", jsonEdgeArray edgesIdx)
        , ("S", jsonNatArray SIdx)
        , ("hull", jsonNatArray hullIdx)
        ]
      IO.println (toString j)

end HeytingLean.CLI.CausalHullMain

def main (argv : List String) : IO Unit :=
  HeytingLean.CLI.CausalHullMain.run argv
