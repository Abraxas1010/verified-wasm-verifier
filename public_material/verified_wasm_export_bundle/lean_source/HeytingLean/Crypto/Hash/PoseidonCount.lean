import HeytingLean.Crypto.Field.BN254

namespace HeytingLean
namespace Crypto
namespace Hash

open HeytingLean.Crypto.Field

structure Ctx where
  count : Nat := 0

abbrev Counter := StateM Ctx

def inc (n := 1) : Counter Unit := do
  let s ← get; set { s with count := s.count + n }

def mulC (x y : Nat) : Counter Nat := do
  inc 1
  pure (mul x y)

def addC (x y : Nat) : Counter Nat := do
  pure (add x y)

def pow5C (x : Nat) : Counter Nat := do
  -- x^5 via 3 multiplications: x2=x*x; x4=x2*x2; x5=x4*x
  let x2 ← mulC x x
  let x4 ← mulC x2 x2
  let x5 ← mulC x4 x
  pure x5

def mds3 (a b c : Nat) : (Nat × Nat × Nat) :=
  -- simple constant MDS (for counting model; constants modeled as free multiplies)
  let m11 := 2; let m12 := 1; let m13 := 1
  let m21 := 1; let m22 := 2; let m23 := 1
  let m31 := 1; let m32 := 1; let m33 := 2
  let r1 := norm (m11*a + m12*b + m13*c)
  let r2 := norm (m21*a + m22*b + m23*c)
  let r3 := norm (m31*a + m32*b + m33*c)
  (r1, r2, r3)

def poseidon3Count (x y : Nat) : Nat :=
  -- hash two field elements into one with width t=3 sponge-like rounds
  let sponge := do
    -- init state (x,y,0)
    let mut s1 := x; let mut s2 := y; let mut s3 := 0
    -- 8 full rounds (S-box on all 3): 3 muls per S-box → 9 muls per round
    for _ in [0:8] do
      s1 ← pow5C s1; s2 ← pow5C s2; s3 ← pow5C s3
      let (r1,r2,r3) := mds3 s1 s2 s3
      s1 := r1; s2 := r2; s3 := r3
    -- 30 partial rounds (S-box on one limb): 3 muls per round
    for _ in [0:30] do
      s1 ← pow5C s1
      let (r1,r2,r3) := mds3 s1 s2 s3
      s1 := r1; s2 := r2; s3 := r3
    pure s1
  let (_out, st) := sponge.run { count := 0 }
  st.count

def merkleLevelCount (left right : Nat) : Nat :=
  poseidon3Count left right

def merkleProofCount (levels : Nat) : Nat :=
  let base := 1 -- start with 1 hash (leaf-to-first)
  base + (levels - 1) * poseidon3Count 0 0

end Hash
end Crypto
end HeytingLean
