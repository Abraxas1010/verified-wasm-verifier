import HeytingLean.LeanCP.RealWorld.CtEqVerified
import HeytingLean.LeanCP.RealWorld.MemcpyVerified

namespace HeytingLean.LeanCP.RealWorld

open HeytingLean.LeanCP

/-- Constant-time copy uses the verified `memcpy` loop body, together with an explicit
syntactic no-branch audit. -/
def ctMemcpyBody : CStmt :=
  memcpyBody

theorem ctMemcpy_noBranch : NoBranch ctMemcpyBody := by
  simp [ctMemcpyBody, memcpyBody, memcpyLoopBody, NoBranch]

theorem ctMemcpy_correct (dstBase srcBase : Nat) (vals : List Int)
    (hdisj : disjointRanges dstBase vals.length srcBase vals.length) :
    ∀ st,
      st.lookupVar "dst" = some (CVal.ptrAddr (dstBase : PtrVal)) →
      st.lookupVar "src" = some (CVal.ptrAddr (srcBase : PtrVal)) →
      st.lookupVar "n" = some (.int (Int.ofNat vals.length)) →
      allocated_s dstBase vals.length st →
      bytesAt_s srcBase vals st →
      ∃ st',
        execStmt (swhileFuel memcpyLoopBody vals.length + 2) ctMemcpyBody st =
          some (.returned (CVal.ptrAddr (dstBase : PtrVal)) st') ∧
        bytesAt_s srcBase vals st' ∧
        bytesAt_s dstBase vals st' := by
  simpa [ctMemcpyBody] using memcpy_correct dstBase srcBase vals hdisj

end HeytingLean.LeanCP.RealWorld
