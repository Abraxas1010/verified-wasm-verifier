/-!
# Graph Spectral "Fourier" (float-based, small finite examples)

Computes a small set of Laplacian eigenvectors via simple power iteration with
orthogonal deflation. Intended for tiny graphs and demo CLIs; the algorithms
are explicit and honest but not optimised for large instances.
-/

namespace HeytingLean
namespace Analysis
namespace Graph

structure Edges where
  n     : Nat
  pairs : Array (Nat × Nat)   -- 0-based endpoints, undirected
deriving Repr

def adjList (g : Edges) : Array (Array Nat) := Id.run do
  let mut out : Array (Array Nat) := Array.replicate g.n (#[] : Array Nat)
  for e in g.pairs do
    let (u,v) := e
    if u < g.n ∧ v < g.n then
      out := out.set! u ((out[u]!).push v)
      out := out.set! v ((out[v]!).push u)
    else ()
  return out

def degree (adj : Array (Array Nat)) : Array Float :=
  adj.map (fun nbrs => Float.ofNat nbrs.size)

def laplacianMul (adj : Array (Array Nat)) (deg : Array Float) (v : Array Float) : Array Float := Id.run do
  let n := v.size
  let mut out := Array.replicate n (0.0 : Float)
  for i in [0:n] do
    let di := deg[i]!
    let mut s : Float := 0.0
    for j in (adj[i]!) do
      s := s + v[j]!
    out := out.set! i (di * (v[i]!) - s)
  return out

def dot (x y : Array Float) : Float := Id.run do
  let n := min x.size y.size
  let mut s : Float := 0.0
  for i in [0:n] do
    s := s + (x[i]!) * (y[i]!)
  return s

def l2norm (x : Array Float) : Float :=
  let s := dot x x
  -- Newton sqrt (few iterations)
  let rec sqrtLoop (y : Float) (t : Nat) : Float :=
    if t = 0 then y else sqrtLoop (0.5 * (y + s / y)) (t-1)
  let y0 := if s ≤ 1.0 then 1.0 else s
  sqrtLoop y0 6

def normalize (x : Array Float) : Array Float := Id.run do
  let nrm := l2norm x
  if nrm == 0.0 then x else x.map (fun a => a / nrm)

def subProj (x u : Array Float) : Array Float := Id.run do
  let a := dot x u
  let b := dot u u
  if b == 0.0 then
    x
  else
    let scale := a / b
    Id.run do
      let n := x.size
      let mut out := x
      for i in [0:n] do
        out := out.set! i ((x[i]!) - scale * (u[i]!))
      out

def powerEigen (adj : Array (Array Nat)) (deg : Array Float)
    (prev : Array (Array Float)) (iters : Nat := 20) : Array Float := Id.run do
  let n := deg.size
  -- init deterministic vector
  let mut v := Array.ofFn (fun i : Fin n => Float.ofNat (i.1 + 1))
  v := normalize v
  for _ in [0:iters] do
    let mut w := laplacianMul adj deg v
    -- deflate
    for u in prev do
      w := subProj w u
    v := normalize w
  return v

def kEigen (g : Edges) (k : Nat) (iters : Nat := 30) : Array (Array Float) := Id.run do
  let adj := adjList g
  let deg := degree adj
  let kk := min k g.n
  let mut out : Array (Array Float) := #[]
  for _ in [0:kk] do
    let v := powerEigen adj deg out iters
    out := out.push v
  return out

def project (vecs : Array (Array Float)) (x : Array Float) : Array Float :=
  vecs.map (fun v => dot x v)

end Graph
end Analysis
end HeytingLean
