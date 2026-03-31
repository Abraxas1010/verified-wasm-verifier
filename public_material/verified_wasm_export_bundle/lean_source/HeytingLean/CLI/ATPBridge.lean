import Lean
import Lean.Data.Json
import HeytingLean.Bridges.CoqLens
import HeytingLean.CLI.Args
import HeytingLean.Util.SHA

/-!
# atp_bridge CLI

Runs the Lean↔Coq Comparison Nucleus bridge, emitting or printing digests.
This v1 focuses on driving the Python emitter and printing the Coq digest.
Future iterations will add Lean/C JSON emissions for parity.
-/

namespace HeytingLean
namespace CLI
namespace ATPBridge

open Lean

structure Args where
  casePath    : Option String := none
  emitCoq     : Bool := false
  emitLean    : Bool := false
  emitC       : Bool := false
  printDigest : Bool := false
  outDir      : Option String := none
deriving Inhabited

private def parseArgs (xs : List String) : Args :=
  let rec go (st : Args) (ys : List String) : Args :=
    match ys with
    | [] => st
    | "--case" :: p :: ys' => go { st with casePath := some p } ys'
    | "--emit-coq" :: ys' => go { st with emitCoq := true } ys'
    | "--emit-lean" :: ys' => go { st with emitLean := true } ys'
    | "--emit-c" :: ys' => go { st with emitC := true } ys'
    | "--print-digest" :: ys' => go { st with printDigest := true } ys'
    | "--out-dir" :: d :: ys' => go { st with outDir := some d } ys'
    | _ :: ys' => go st ys'
  go {} xs

def run (argv : List String) : IO Unit := do
  let args := parseArgs (HeytingLean.CLI.stripLakeArgs argv)
  -- Helper: read case JSON into atoms/tests (v1: bool3)
  let caseOk ← match args.casePath with
    | none => pure false
    | some p => do
        let fp := System.FilePath.mk p
        if !(← fp.pathExists) then
          IO.eprintln s!"case file not found: {p}"; pure false
        else pure true

  -- Compute Lean ops JSON if case provided
  let leanOpsJson? ← if !caseOk then pure (none : Option String) else do
    let p := System.FilePath.mk (args.casePath.getD "")
    let s ← IO.FS.readFile p
    let j ← match Json.parse s with | .ok j => pure j | .error _ => throw <| IO.userError "invalid case JSON"
    let o ← match j.getObj? with | .ok o => pure o | .error _ => throw <| IO.userError "invalid case object"
    -- atoms
    let atomsL : List String := match o.get? "atoms" with
      | some (.arr a) => a.foldl (fun acc j => match j with | .str s => s :: acc | _ => acc) ([] : List String) |>.reverse
      | _ => []
    if atomsL.isEmpty then throw <| IO.userError "missing atoms"
    -- logic kind (default boolean)
    let logicKind := match o.get? "logic_kind" with | some (.str s) => s | _ => "boolean"
    if logicKind ≠ "boolean" then
      throw <| IO.userError s!"ERROR: logic_kind \"{logicKind}\" not supported in compute harness. This harness assumes Boolean implication (a ⇒ b ≡ ¬a ∨ b)."
    let idxOf (lab : String) : Nat :=
      let rec go (xs : List String) (i : Nat) : Nat :=
        match xs with
        | [] => 0
        | y::ys => if y = lab then i else go ys (i+1)
      go atomsL 0
    let nBits := atomsL.length
    let toMask (arr : List Json) : Nat :=
      let labs := arr.foldl (fun acc j => match j with | .str s => s :: acc | _ => acc) ([] : List String) |>.reverse
      labs.foldl (fun m s => m ||| (Nat.shiftLeft 1 (idxOf s))) 0
    let labelsOf (mask : Nat) : Array Json :=
      let rec loop (i : Nat) (acc : List String) : List String :=
        if h : i < nBits then
          let bit := Nat.shiftLeft 1 i
          let acc' := if (mask &&& bit) ≠ 0 then (acc ++ [atomsL[i]!]) else acc
          loop (i+1) acc'
        else acc
      let labs := loop 0 ([] : List String)
      (Array.mk <| labs.map Json.str)
    let getArrL (k : String) : List Json :=
      match o.get? k with | some (.arr a) => a.toList | _ => []
    -- nucleus param p
    let pMask := (match o.get? "nucleus" with
      | some (.obj m) => (match m.get? "p" with | some (.arr a) => toMask a.toList | _ => 0)
      | _ => 0)
    let close (x : Nat) : Nat := x ||| pMask
    -- tests (collect then sort canonically by (S_mask, T_mask))
    let testsL := getArrL "tests"
    let rec complementWithin (mask : Nat) (i : Nat) (acc : Nat) : Nat :=
      if h : i < nBits then
        let bit := Nat.shiftLeft 1 i
        let acc' := if (mask &&& bit) ≠ 0 then acc else (acc ||| bit)
        complementWithin mask (i+1) acc'
      else acc
    let notWithin (mask : Nat) : Nat := complementWithin mask 0 0
    -- canonical string emit to match C tool ordering
    let encSetStr (mask : Nat) : String :=
      let arr := labelsOf mask
      let parts := (arr.toList).map (fun j => match j with | .str s => "\"" ++ s ++ "\"" | _ => "")
      s!"[" ++ String.intercalate "," parts ++ "]"
    -- collect tests with masks
    let rec collect (xs : List Json) (acc : List (Nat × Nat × List Json × List Json)) : List (Nat × Nat × List Json × List Json) :=
      match xs with
      | [] => acc
      | t :: ts =>
        let acc' := match t.getObj? with
          | .ok tobj =>
              let sArrL := match tobj.get? "S" with | some (.arr a) => a.toList | _ => []
              let tArrL := match tobj.get? "T" with | some (.arr a) => a.toList | _ => []
              let sMask := toMask sArrL
              let tMask := toMask tArrL
              (sMask, tMask, sArrL, tArrL) :: acc
          | .error _ => acc
        collect ts acc'
    let pairs := collect testsL []
    let ltPair (x y : (Nat × Nat × List Json × List Json)) : Bool :=
      let s1 := x.fst; let t1 := x.snd.fst
      let s2 := y.fst; let t2 := y.snd.fst
      if s1 == s2 then t1 < t2 else s1 < s2
    let rec ins (x : (Nat × Nat × List Json × List Json)) (xs : List (Nat × Nat × List Json × List Json)) : List (Nat × Nat × List Json × List Json) :=
      match xs with
      | [] => [x]
      | y :: ys => if ltPair x y then x :: xs else y :: ins x ys
    let pairsSorted := pairs.foldl (fun acc e => ins e acc) ([] : List (Nat × Nat × List Json × List Json))
    let rec buildItems (ps : List (Nat × Nat × List Json × List Json)) (acc : List String) : List String :=
      match ps with
      | [] => acc.reverse
      | p :: ps' =>
        let sMask := p.fst
        let tMask := p.snd.fst
        let aMask := close sMask
        let bMask := close tMask
        let andMask := aMask &&& bMask
        let orMask  := close (aMask ||| bMask)
        let impMask := close ((notWithin aMask) ||| bMask)
        let negMask := close (notWithin aMask)
        let sSet := encSetStr sMask
        let tSet := encSetStr tMask
        let aSet := encSetStr aMask
        let bSet := encSetStr bMask
        let andSet := encSetStr andMask
        let orSet  := encSetStr orMask
        let impSet := encSetStr impMask
        let negSet := encSetStr negMask
        let objStr := "{" ++
          s!"\"S\":{sSet},\"T\":{tSet},\"A\":{aSet},\"B\":{bSet},\"andR\":{andSet},\"orR\":{orSet},\"impR\":{impSet},\"negR\":{negSet}" ++ "}"
        buildItems ps' (objStr :: acc)
    let testsItems := buildItems pairsSorted []
    let testsStr := "[" ++ String.intercalate "," testsItems ++ "]"
    let nid := s!"join_const_{pMask}"
    let canon := "{\"carrier_id\":\"bool" ++ toString nBits ++ "\",\"nucleus_id\":\"" ++ nid ++ "\",\"tests\":" ++ testsStr ++ "}"
    pure (some canon)

  -- Write Lean ops if requested
  if args.emitLean then
    match leanOpsJson? with
    | none => IO.eprintln "no case loaded; cannot emit lean ops"
    | some s =>
        let outBase := args.outDir.getD "artifacts"
        -- choose output filename based on atom count (defaults to 3 when case missing)
        let nStr := match leanOpsJson? with
          | some s =>
              -- hack-free parse: detect carrier_id we just embedded
              let marker := "\"carrier_id\":\"bool"
              match s.splitOn marker with
              | _ :: rest =>
                  match rest with
                  | seg :: _ =>
                      let digits := seg.takeWhile (fun c => c.isDigit)
                      if digits.isEmpty then "3" else digits
                  | _ => "3"
              | _ => "3"
          | none => "3"
        let path := (System.FilePath.mk outBase).join (s!"lean_ops_bool{nStr}.json")
        if let some p := path.parent then IO.FS.createDirAll p else pure ()
        IO.FS.writeFile path s
        if args.printDigest then
          -- Prefer C digest tool for real SHA-256 if available
          let cwd ← IO.currentDir
          let tool1 := cwd / System.FilePath.mk "../c/bin/atp_cert_digest"
          let tool2 := cwd / System.FilePath.mk "c/bin/atp_cert_digest"
          let tool := if (← tool1.pathExists) then tool1 else tool2
          if (← tool.pathExists) then
            let out ← IO.Process.output { cmd := tool.toString, args := #["--from", path.toString] }
            if out.exitCode == 0 then IO.print out.stdout else IO.println ""
          else
            let h ← HeytingLean.Util.sha256HexOfStringIO s
            IO.println h
          return ()
        else
          IO.println s!"wrote {path}"
          return ()

  -- Else: Coq certificate path
  let outPath := System.FilePath.mk "certs/cert.json"
  let cert ← HeytingLean.Bridges.CoqLens.getCertificate outPath
  let coqJsonStr := (Json.mkObj [
    ("carrier_id", Json.str cert.carrierId),
    ("nucleus_id", Json.str cert.nucleusId),
    ("proofs", Json.mkObj [
      ("rt1", Json.bool cert.proofs_rt1),
      ("rt2", Json.arr (cert.proofs_rt2.map Json.str |>.toArray)),
      ("triad", Json.bool cert.proofs_triad)
    ]),
    ("lemmas", Json.arr (cert.lemmas.map Json.str |>.toArray)),
    ("public_digest", Json.str cert.publicDigest)
  ]).compress
  if args.emitCoq then
    IO.println coqJsonStr
    return ()
  if args.printDigest then
    -- Default digest: Lean ops if available, otherwise Coq public_digest
    match leanOpsJson? with
    | some s => IO.println (← HeytingLean.Util.sha256HexOfStringIO s)
    | none   => IO.println cert.publicDigest
  else
    IO.println coqJsonStr

end ATPBridge
end CLI
end HeytingLean

def main (argv : List String) : IO Unit := HeytingLean.CLI.ATPBridge.run argv
