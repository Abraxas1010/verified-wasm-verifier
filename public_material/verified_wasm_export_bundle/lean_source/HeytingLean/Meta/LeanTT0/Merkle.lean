import HeytingLean.Meta.LeanTT0.Hash
import HeytingLean.Meta.LeanTT0.Rules
import HeytingLean.Meta.LeanTT0.Trace

namespace HeytingLean.Meta.LeanTT0

private def leBA (a b : ByteArray) : Bool := Id.run do
  let as := a.data; let bs := b.data
  let la := as.size; let lb := bs.size
  let m := if la < lb then la else lb
  for i in [0:m] do
    let ai := as[i]!; let bi := bs[i]!
    if ai ≠ bi then return ai.toNat ≤ bi.toNat
  return la ≤ lb

private def cat (a b : ByteArray) : ByteArray := ByteArray.mk (a.data ++ b.data)

def catSorted (a b : ByteArray) : ByteArray := if leBA a b then cat a b else cat b a

def merkleParent (a b : ByteArray) : ByteArray :=
  let payload := catSorted a b
  H "LoF.Merkle.Node|" payload

def merkleRoot (leaves : List ByteArray) : ByteArray :=
  let rec iter (fuel : Nat) (xs : List ByteArray) : ByteArray :=
    match xs with
    | []      => sha256 "".toUTF8
    | [x]     => x
    | _       =>
      if fuel = 0 then sha256 "".toUTF8 else
        let rec mkLevel : List ByteArray → List ByteArray
          | [] => []
          | [x] => [x]
          | a::b::rest => merkleParent a b :: mkLevel rest
        iter (fuel - 1) (mkLevel xs)
  iter (leaves.length + 1) leaves

/- If `path` is empty, succeeds iff `leaf = root`. Otherwise fold sorted parents. -/
def verifyProof (root leaf : ByteArray) (path : List ByteArray) : Bool :=
  let acc := path.foldl (fun acc sib => merkleParent acc sib) leaf
  acc == root

/-- Construct a membership proof path for `leaf` given the full `leaves` set.
    Returns `none` when the leaf is not present. -/
def mkProof (leaves : List ByteArray) (leaf : ByteArray) : Option (List ByteArray) :=
  match leaves with
  | []      => none
  | [x]     => if x == leaf then some [] else none
  | x::y::_ =>
      if x == leaf then some [y]
      else if y == leaf then some [x]
      else none

/- Step and transcript digests -/
def stepDigest (s : TraceStep) : ByteArray :=
  -- H("LoF.TT0.Step|" || ruleId.hash || before || after)
  let r := (ruleId s.rule).hash
  let acc := ByteArray.mk (r.data ++ s.before.data ++ s.after.data)
  H "LoF.TT0.Step|" acc

def transcriptRoot (steps : List TraceStep) : ByteArray :=
  merkleRoot (steps.map stepDigest)

/-- Poseidon-styled (domain-separated) variants to support dual roots in JSON.
    These use the same sha256 backend with distinct domain tags to avoid
    cross-collision and serve as a compatibility layer until real Poseidon lands. -/
def poseidonNode (a b : ByteArray) : ByteArray :=
  let payload := catSorted a b
  H "LoF.Poseidon.Node|" payload

def poseidonRoot (leaves : List ByteArray) : ByteArray :=
  let rec iter (fuel : Nat) (xs : List ByteArray) : ByteArray :=
    match xs with
    | []      => H "LoF.Poseidon.Empty|" ByteArray.empty
    | [x]     => x
    | _       =>
      if fuel = 0 then H "LoF.Poseidon.OOM|" ByteArray.empty else
        let rec mkLevel : List ByteArray → List ByteArray
          | [] => []
          | [x] => [x]
          | a::b::rest => poseidonNode a b :: mkLevel rest
        iter (fuel - 1) (mkLevel xs)
  iter (leaves.length + 1) leaves

def stepDigestPoseidon (s : TraceStep) : ByteArray :=
  let r := (ruleId s.rule).hash
  let acc := ByteArray.mk (r.data ++ s.before.data ++ s.after.data)
  H "LoF.Poseidon.Step|" acc

def transcriptRootPoseidon (steps : List TraceStep) : ByteArray :=
  poseidonRoot (steps.map stepDigestPoseidon)

end HeytingLean.Meta.LeanTT0
