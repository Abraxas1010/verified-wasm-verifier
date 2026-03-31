namespace HeytingLean
namespace Util

/-- Iterate a function `f` `k` times starting from `a`. -/
def iterateN : Nat → (α → α) → α → α
  | 0,     f, a => a
  | n + 1, f, a => iterateN n f (f a)

/-- Iterate `f` up to `k` steps, returning the number of steps taken,
    the final value, and a flag indicating whether a fixed point was
    reached (i.e., `f out = out`). -/
def iterateUntilFix [DecidableEq α]
    (k : Nat) (f : α → α) (a : α) : Nat × α × Bool :=
  let rec loop : Nat → α → Nat × α × Bool
  | 0, x => (0, x, f x = x)
  | Nat.succ i, x =>
      let x' := f x
      if h : x' = x then
        (0, x, True)
      else
        let (steps, out, done) := loop i x'
        (steps.succ, out, done)
  loop k a

end Util
end HeytingLean
