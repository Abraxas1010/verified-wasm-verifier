/-!
# Walsh–Hadamard transform (integer, power-of-two length)

Simple in-place style transform on arrays of `Int`. This is intended for tiny
inputs (demo/CLI). Normalization is omitted (unscaled transform).
-/

namespace HeytingLean
namespace Analysis

private def isPow2 (n : Nat) : Bool :=
  n ≠ 0 ∧ (n &&& (n - 1)) = 0

private def pow2Exp (n : Nat) : Nat :=
  if n ≤ 1 then
    0
  else
    pow2Exp (n / 2) + 1
termination_by n
decreasing_by
  -- `n / 2 < n` for all `n > 1`.
  have hn : 1 < n := Nat.lt_of_not_ge (show ¬ n ≤ 1 from by simpa using ‹¬ n ≤ 1›)
  have hn0 : 0 < n := Nat.lt_trans Nat.zero_lt_one hn
  simpa using Nat.div_lt_self hn0 (by decide : 1 < 2)

def walshCore (arr : Array Int) : Array Int := Id.run do
  let n := arr.size
  let mut a := arr
  let stages := pow2Exp n
  for k in [0:stages] do
    let len := Nat.pow 2 k
    let blockSize := 2 * len
    let numBlocks := n / blockSize
    for b in [0:numBlocks] do
      let i := b * blockSize
      for j in [0:len] do
        let idx := i + j
        let u := a[idx]!
        let v := a[idx + len]!
        a := a.set! idx (u + v)
        a := a.set! (idx + len) (u - v)
  return a

def walsh (arr : Array Int) : Array Int :=
  if isPow2 arr.size then walshCore arr else arr

end Analysis
end HeytingLean
