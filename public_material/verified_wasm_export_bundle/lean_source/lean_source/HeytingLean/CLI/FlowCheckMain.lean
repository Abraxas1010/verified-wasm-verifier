import Lean
import HeytingLean.Metrics.Curvature
import HeytingLean.Bridges.Flow

open HeytingLean.Metrics

namespace HeytingLean.CLI

private def parseArg (xs : List String) (flag : String) : Option String :=
  match xs with
  | [] => none
  | x::y::rest => if x = flag then some y else parseArg (y::rest) flag
  | _ => none

private def parsePoint (s : String) : FlowPoint :=
  s.splitOn "," |>.foldl (init := #[]) (fun acc t => match t.toInt? with | some v => acc.push (Float.ofInt v) | none => acc)

private def parsePoints (s : String) : Array FlowPoint :=
  s.splitOn ";" |>.foldl (init := #[]) (fun acc row =>
    let p := parsePoint row
    if p.isEmpty then acc else acc.push p)

private def floatStr (x : Float) : String := toString x

def main (argv : List String) : IO Unit := do
  let ptsStr := (parseArg argv "--pts").getD "0,0;1,0;1,1;0,0"
  let pts := parsePoints ptsStr
  let n := pts.size
  if n < 3 then
    IO.println "{\"error\":\"need at least 3 points\"}"
    return
  let kTolI := (parseArg argv "--kTol").bind (·.toInt?) |>.getD 2
  let vTolI := (parseArg argv "--vTol").bind (·.toInt?) |>.getD 2
  let kTol : Float := Float.ofInt kTolI
  let vTol : Float := Float.ofInt vTolI
  -- Curvatures over triples
  let mut curvs : Array Float := #[]
  for i in [0:n-2] do
    if i+2 ≤ n then
      let k := mengerCurvature pts[i]! pts[i+1]! pts[i+2]!
      curvs := curvs.push k
  let kCount := curvs.size
  let kSum := curvs.foldl (init := 0.0) (· + ·)
  let kMax := curvs.foldl (init := 0.0) (fun m v => if v > m then v else m)
  let kAvg := if kCount = 0 then 0.0 else kSum / (Float.ofNat kCount)
  -- Velocity magnitudes
  let v := finiteDiff pts
  let mut vMagSum : Float := 0.0
  for dv in v do
    -- l2Dist to zero is just the norm
    let zero : FlowPoint := Array.replicate dv.size 0.0
    vMagSum := vMagSum + l2Dist dv zero
  let vAvg := if v.size = 0 then 0.0 else vMagSum / (Float.ofNat v.size)
  -- loop criteria (position and direction cosine)
  let posTolI := (parseArg argv "--posTol").bind (·.toInt?) |>.getD 0
  let dirCosTolI := (parseArg argv "--dirCosTol").bind (·.toInt?) |>.getD 80 -- percent
  let posTol : Float := Float.ofInt posTolI
  let dirCosTol : Float := (Float.ofInt dirCosTolI) / 100.0
  let minPerimI := (parseArg argv "--minPerim").bind (·.toInt?) |>.getD 0
  let minAreaI  := (parseArg argv "--minArea").bind (·.toInt?) |>.getD 0
  let minPerim : Float := Float.ofInt minPerimI
  let minArea  : Float := Float.ofInt minAreaI
  let loopOk := HeytingLean.Bridges.Flow.isLoop posTol dirCosTol pts
  let loopStrictOk := HeytingLean.Bridges.Flow.isLoopStrict posTol dirCosTol minPerim minArea pts
  let ok := (kMax ≤ kTol) && (vAvg ≤ vTol) && loopStrictOk
  let json := "{" ++ s!"\"n\":{n}," ++ s!"\"kAvg\":{floatStr kAvg}," ++ s!"\"kMax\":{floatStr kMax}," ++ s!"\"vAvg\":{floatStr vAvg}," ++ s!"\"kTol\":{kTolI}," ++ s!"\"vTol\":{vTolI}," ++ s!"\"posTol\":{posTolI}," ++ s!"\"dirCosTolPct\":{dirCosTolI}," ++ s!"\"minPerim\":{minPerimI}," ++ s!"\"minArea\":{minAreaI}," ++ s!"\"loopOk\":{loopOk}," ++ s!"\"loopStrictOk\":{loopStrictOk}," ++ s!"\"ok\":{ok}}"
  IO.println json

end HeytingLean.CLI

def main (argv : List String) : IO Unit := HeytingLean.CLI.main argv
