import HeytingLean.LeanCP.RealWorld.Support
import HeytingLean.LeanCP.RealWorld.MemcpyVerified
import HeytingLean.LeanCP.RealWorld.MemsetVerified
import HeytingLean.LeanCP.Modular.Linking
import Mathlib.Tactic

namespace HeytingLean.LeanCP.RealWorld

open HeytingLean.LeanCP
open HeytingLean.LeanCP.Modular

set_option linter.unnecessarySimpa false

/-- Fixed-layout two-cell record predicate used by the composition slice. -/
abbrev pairAt_s (base : Nat) (x y : Int) : SProp :=
  bytesAt_s base [x, y]

theorem pairAt_s_updateVar (base : Nat) (x y : Int) (st : CState)
    (name : String) (v : CVal) :
    pairAt_s base x y (st.updateVar name v) ↔ pairAt_s base x y st := by
  simpa [pairAt_s] using bytesAt_s_updateVar base [x, y] st name v

theorem pairAt_s_restoreCallerState (base : Nat) (x y : Int) (caller callee : CState) :
    pairAt_s base x y (restoreCallerState caller callee) ↔ pairAt_s base x y callee := by
  rfl

theorem pairAt_s_of_filled_zero (base : Nat) (st : CState)
    (hfilled : filled_s base 2 0 st) :
    pairAt_s base 0 0 st := by
  intro i v hv
  have hi : i < 2 := by
    simpa using (List.getElem?_eq_some_iff.mp hv).1
  interval_cases i <;> simp at hv
  · cases hv
    simpa using hfilled 0 (by decide)
  · cases hv
    simpa using hfilled 1 (by decide)

def memcpyPairFuel : Nat :=
  swhileFuel memcpyLoopBody 2 + 2

def memsetPairFuel : Nat :=
  swhileFuel memsetLoopBody 2 + 2

def memcpyPairSpec (dstBase srcBase : Nat) (x y : Int) : SFunSpec where
  name := "memcpy"
  params := [("dst", .ptr .int), ("src", .ptr .int), ("n", .int)]
  retType := .ptr .int
  pre := fun st =>
    disjointRanges dstBase 2 srcBase 2 ∧
    st.lookupVar "dst" = some (CVal.ptrAddr (dstBase : PtrVal)) ∧
    st.lookupVar "src" = some (CVal.ptrAddr (srcBase : PtrVal)) ∧
    st.lookupVar "n" = some (.int 2) ∧
    allocated_s dstBase 2 st ∧
    pairAt_s srcBase x y st
  post := fun ret st =>
    ret = CVal.ptrAddr (dstBase : PtrVal) ∧
    pairAt_s srcBase x y st ∧
    pairAt_s dstBase x y st
  body := memcpyBody

def memsetPairSpec (base : Nat) (fill : Int) : SFunSpec where
  name := "memset"
  params := [("dst", .ptr .int), ("value", .int), ("n", .int)]
  retType := .ptr .int
  pre := fun st =>
    st.lookupVar "dst" = some (CVal.ptrAddr (base : PtrVal)) ∧
    st.lookupVar "value" = some (.int fill) ∧
    st.lookupVar "n" = some (.int 2) ∧
    allocated_s base 2 st
  post := fun ret st =>
    ret = CVal.ptrAddr (base : PtrVal) ∧
    filled_s base 2 fill st
  body := memsetBody

def structCopyBody : CStmt :=
  .ret (.call "memcpy" [.var "dst", .var "src", .intLit 2])

def structCopySpec (dstBase srcBase : Nat) (x y : Int) : SFunSpec where
  name := "struct_copy"
  params := [("dst", .ptr .int), ("src", .ptr .int)]
  retType := .ptr .int
  pre := fun st =>
    disjointRanges dstBase 2 srcBase 2 ∧
    st.lookupVar "dst" = some (CVal.ptrAddr (dstBase : PtrVal)) ∧
    st.lookupVar "src" = some (CVal.ptrAddr (srcBase : PtrVal)) ∧
    allocated_s dstBase 2 st ∧
    pairAt_s srcBase x y st
  post := fun ret st =>
    ret = CVal.ptrAddr (dstBase : PtrVal) ∧
    pairAt_s srcBase x y st ∧
    pairAt_s dstBase x y st
  body := structCopyBody

def bufferStoreBody : CStmt :=
  .ret (.call "struct_copy" [.var "dst", .var "src"])

def bufferStoreSpec (bufBase srcBase : Nat) (x y : Int) : SFunSpec where
  name := "buffer_store"
  params := [("dst", .ptr .int), ("src", .ptr .int)]
  retType := .ptr .int
  pre := fun st =>
    disjointRanges bufBase 2 srcBase 2 ∧
    st.lookupVar "dst" = some (CVal.ptrAddr (bufBase : PtrVal)) ∧
    st.lookupVar "src" = some (CVal.ptrAddr (srcBase : PtrVal)) ∧
    allocated_s bufBase 2 st ∧
    pairAt_s srcBase x y st
  post := fun ret st =>
    ret = CVal.ptrAddr (bufBase : PtrVal) ∧
    pairAt_s srcBase x y st ∧
    pairAt_s bufBase x y st
  body := bufferStoreBody

def bufferClearBody : CStmt :=
  .ret (.call "memset" [.var "dst", .intLit 0, .intLit 2])

def bufferClearSpec (bufBase : Nat) : SFunSpec where
  name := "buffer_clear"
  params := [("dst", .ptr .int)]
  retType := .ptr .int
  pre := fun st =>
    st.lookupVar "dst" = some (CVal.ptrAddr (bufBase : PtrVal)) ∧
    allocated_s bufBase 2 st
  post := fun ret st =>
    ret = CVal.ptrAddr (bufBase : PtrVal) ∧
    pairAt_s bufBase 0 0 st
  body := bufferClearBody

def structCopyVerifyEnv (dstBase srcBase : Nat) (x y : Int) : FunEnv
  | "memcpy" => some (memcpyPairSpec dstBase srcBase x y)
  | _ => none

def bufferStoreVerifyEnv (bufBase srcBase : Nat) (x y : Int) : FunEnv
  | "struct_copy" => some (structCopySpec bufBase srcBase x y)
  | _ => none

def bufferClearVerifyEnv (bufBase : Nat) : FunEnv
  | "memset" => some (memsetPairSpec bufBase 0)
  | _ => none

private theorem memcpyPair_entry_lookup_dst (st : CState) (dstBase srcBase : Nat) (x y : Int) :
    (callEntryState st (memcpyPairSpec dstBase srcBase x y)
      [CVal.ptrAddr (dstBase : PtrVal), CVal.ptrAddr (srcBase : PtrVal), .int 2]).lookupVar "dst" =
      some (CVal.ptrAddr (dstBase : PtrVal)) := by
  simp [callEntryState, memcpyPairSpec, bindCallEnv, CState.lookupVar]

private theorem memcpyPair_entry_lookup_src (st : CState) (dstBase srcBase : Nat) (x y : Int) :
    (callEntryState st (memcpyPairSpec dstBase srcBase x y)
      [CVal.ptrAddr (dstBase : PtrVal), CVal.ptrAddr (srcBase : PtrVal), .int 2]).lookupVar "src" =
      some (CVal.ptrAddr (srcBase : PtrVal)) := by
  simp [callEntryState, memcpyPairSpec, bindCallEnv, CState.lookupVar, List.lookup]

private theorem memcpyPair_entry_lookup_n (st : CState) (dstBase srcBase : Nat) (x y : Int) :
    (callEntryState st (memcpyPairSpec dstBase srcBase x y)
      [CVal.ptrAddr (dstBase : PtrVal), CVal.ptrAddr (srcBase : PtrVal), .int 2]).lookupVar "n" =
      some (.int 2) := by
  simp [callEntryState, memcpyPairSpec, bindCallEnv, CState.lookupVar, List.lookup]

private theorem structCopy_entry_lookup_dst (st : CState) (dstBase srcBase : Nat) (x y : Int) :
    (callEntryState st (structCopySpec dstBase srcBase x y)
      [CVal.ptrAddr (dstBase : PtrVal), CVal.ptrAddr (srcBase : PtrVal)]).lookupVar "dst" =
      some (CVal.ptrAddr (dstBase : PtrVal)) := by
  simp [callEntryState, structCopySpec, bindCallEnv, CState.lookupVar]

private theorem structCopy_entry_lookup_src (st : CState) (dstBase srcBase : Nat) (x y : Int) :
    (callEntryState st (structCopySpec dstBase srcBase x y)
      [CVal.ptrAddr (dstBase : PtrVal), CVal.ptrAddr (srcBase : PtrVal)]).lookupVar "src" =
      some (CVal.ptrAddr (srcBase : PtrVal)) := by
  simp [callEntryState, structCopySpec, bindCallEnv, CState.lookupVar, List.lookup]

private theorem memsetPair_entry_lookup_dst (st : CState) (base : Nat) (fill : Int) :
    (callEntryState st (memsetPairSpec base fill)
      [CVal.ptrAddr (base : PtrVal), .int fill, .int 2]).lookupVar "dst" =
      some (CVal.ptrAddr (base : PtrVal)) := by
  simp [callEntryState, memsetPairSpec, bindCallEnv, CState.lookupVar]

private theorem memsetPair_entry_lookup_value (st : CState) (base : Nat) (fill : Int) :
    (callEntryState st (memsetPairSpec base fill)
      [CVal.ptrAddr (base : PtrVal), .int fill, .int 2]).lookupVar "value" =
      some (.int fill) := by
  simp [callEntryState, memsetPairSpec, bindCallEnv, CState.lookupVar, List.lookup]

private theorem memsetPair_entry_lookup_n (st : CState) (base : Nat) (fill : Int) :
    (callEntryState st (memsetPairSpec base fill)
      [CVal.ptrAddr (base : PtrVal), .int fill, .int 2]).lookupVar "n" =
      some (.int 2) := by
  simp [callEntryState, memsetPairSpec, bindCallEnv, CState.lookupVar, List.lookup]

/-- Specialized leaf witness: accepted `memcpy` theorem restricted to the fixed
two-cell record surface used by the composition slice. -/
theorem memcpy_pair_correct (dstBase srcBase : Nat) (x y : Int) :
    ∀ st,
      (memcpyPairSpec dstBase srcBase x y).pre st →
      ∃ st',
        execStmt memcpyPairFuel memcpyBody st =
          some (.returned (CVal.ptrAddr (dstBase : PtrVal)) st') ∧
        (memcpyPairSpec dstBase srcBase x y).post (CVal.ptrAddr (dstBase : PtrVal)) st' := by
  intro st hpre
  rcases hpre with ⟨hdisj, hdst, hsrc, hn, halloc, hsrcPair⟩
  rcases memcpy_correct dstBase srcBase [x, y] hdisj st hdst hsrc
      (by simpa using hn) halloc hsrcPair with ⟨st', hexec, hsrcPost, hdstPost⟩
  exact ⟨st', hexec, ⟨rfl, hsrcPost, hdstPost⟩⟩

/-- Specialized leaf witness: accepted `memset` theorem restricted to the
two-cell surface used by `buffer_clear`. -/
theorem memset_pair_correct (base : Nat) (fill : Int) :
    ∀ st,
      (memsetPairSpec base fill).pre st →
      ∃ st',
        execStmt memsetPairFuel memsetBody st =
          some (.returned (CVal.ptrAddr (base : PtrVal)) st') ∧
        (memsetPairSpec base fill).post (CVal.ptrAddr (base : PtrVal)) st' := by
  intro st hpre
  rcases hpre with ⟨hdst, hval, hn, halloc⟩
  rcases memset_correct base 2 fill st hdst hval (by simpa using hn) halloc with ⟨st', hexec, hfilled⟩
  exact ⟨st', hexec, ⟨rfl, hfilled⟩⟩

theorem structCopy_call_memcpy (dstBase srcBase : Nat) (x y : Int) :
    ∀ st,
      (structCopySpec dstBase srcBase x y).pre st →
      swpCall (structCopyVerifyEnv dstBase srcBase x y) "memcpy"
        [.var "dst", .var "src", .intLit 2] (structCopySpec dstBase srcBase x y).post st := by
  intro st hpre
  rcases hpre with ⟨hdisj, hdst, hsrc, halloc, hpair⟩
  apply swpCall_intro (funEnv := structCopyVerifyEnv dstBase srcBase x y) (fname := "memcpy")
    (args := [.var "dst", .var "src", .intLit 2]) (spec := memcpyPairSpec dstBase srcBase x y)
    (vals := [CVal.ptrAddr (dstBase : PtrVal), CVal.ptrAddr (srcBase : PtrVal), .int 2])
    (Q := (structCopySpec dstBase srcBase x y).post)
  · simp [structCopyVerifyEnv]
  · simp [evalArgs, evalExpr, evalStaticExpr, hdst, hsrc]
  · simp [memcpyPairSpec]
  · refine ⟨hdisj, memcpyPair_entry_lookup_dst st dstBase srcBase x y,
      memcpyPair_entry_lookup_src st dstBase srcBase x y,
      memcpyPair_entry_lookup_n st dstBase srcBase x y, ?_, ?_⟩
    · simpa [callEntryState, memcpyPairSpec] using halloc
    · simpa [pairAt_s, callEntryState, memcpyPairSpec] using hpair
  · intro ret st' hpost
    rcases hpost with ⟨hret, hsrcPost, hdstPost⟩
    exact ⟨hret, (pairAt_s_restoreCallerState srcBase x y st st').2 hsrcPost,
      (pairAt_s_restoreCallerState dstBase x y st st').2 hdstPost⟩

theorem structCopy_sgenVCFull (dstBase srcBase : Nat) (x y : Int) :
    sgenVCFull (structCopyVerifyEnv dstBase srcBase x y) (structCopySpec dstBase srcBase x y) := by
  intro st hpre
  simpa [structCopyBody, swpFull] using structCopy_call_memcpy dstBase srcBase x y st hpre

theorem bufferStore_call_structCopy (bufBase srcBase : Nat) (x y : Int) :
    ∀ st,
      (bufferStoreSpec bufBase srcBase x y).pre st →
      swpCall (bufferStoreVerifyEnv bufBase srcBase x y) "struct_copy"
        [.var "dst", .var "src"] (bufferStoreSpec bufBase srcBase x y).post st := by
  intro st hpre
  rcases hpre with ⟨hdisj, hdst, hsrc, halloc, hpair⟩
  apply swpCall_intro (funEnv := bufferStoreVerifyEnv bufBase srcBase x y) (fname := "struct_copy")
    (args := [.var "dst", .var "src"]) (spec := structCopySpec bufBase srcBase x y)
    (vals := [CVal.ptrAddr (bufBase : PtrVal), CVal.ptrAddr (srcBase : PtrVal)])
    (Q := (bufferStoreSpec bufBase srcBase x y).post)
  · simp [bufferStoreVerifyEnv]
  · simp [evalArgs, hdst, hsrc]
  · simp [structCopySpec]
  · refine ⟨hdisj, structCopy_entry_lookup_dst st bufBase srcBase x y,
      structCopy_entry_lookup_src st bufBase srcBase x y, ?_, ?_⟩
    · simpa [callEntryState, structCopySpec] using halloc
    · simpa [pairAt_s, callEntryState, structCopySpec] using hpair
  · intro ret st' hpost
    rcases hpost with ⟨hret, hsrcPost, hbufPost⟩
    exact ⟨hret, (pairAt_s_restoreCallerState srcBase x y st st').2 hsrcPost,
      (pairAt_s_restoreCallerState bufBase x y st st').2 hbufPost⟩

theorem bufferStore_sgenVCFull (bufBase srcBase : Nat) (x y : Int) :
    sgenVCFull (bufferStoreVerifyEnv bufBase srcBase x y) (bufferStoreSpec bufBase srcBase x y) := by
  intro st hpre
  simpa [bufferStoreBody, swpFull] using bufferStore_call_structCopy bufBase srcBase x y st hpre

theorem bufferClear_call_memset (bufBase : Nat) :
    ∀ st,
      (bufferClearSpec bufBase).pre st →
      swpCall (bufferClearVerifyEnv bufBase) "memset"
        [.var "dst", .intLit 0, .intLit 2] (bufferClearSpec bufBase).post st := by
  intro st hpre
  rcases hpre with ⟨hdst, halloc⟩
  apply swpCall_intro (funEnv := bufferClearVerifyEnv bufBase) (fname := "memset")
    (args := [.var "dst", .intLit 0, .intLit 2]) (spec := memsetPairSpec bufBase 0)
    (vals := [CVal.ptrAddr (bufBase : PtrVal), .int 0, .int 2])
    (Q := (bufferClearSpec bufBase).post)
  · simp [bufferClearVerifyEnv]
  · simp [evalArgs, evalExpr, evalStaticExpr, hdst]
  · simp [memsetPairSpec]
  · refine ⟨memsetPair_entry_lookup_dst st bufBase 0,
      memsetPair_entry_lookup_value st bufBase 0,
      memsetPair_entry_lookup_n st bufBase 0, ?_⟩
    simpa [callEntryState, memsetPairSpec] using halloc
  · intro ret st' hpost
    rcases hpost with ⟨hret, hfilled⟩
    exact ⟨hret, pairAt_s_of_filled_zero bufBase (restoreCallerState st st')
      (by simpa [restoreCallerState] using hfilled)⟩

theorem bufferClear_sgenVCFull (bufBase : Nat) :
    sgenVCFull (bufferClearVerifyEnv bufBase) (bufferClearSpec bufBase) := by
  intro st hpre
  simpa [bufferClearBody, swpFull] using bufferClear_call_memset bufBase st hpre

def structCopyProc (dstBase srcBase : Nat) (x y : Int) : VerifiedProc where
  spec := structCopySpec dstBase srcBase x y
  verifyEnv := structCopyVerifyEnv dstBase srcBase x y
  sound := by
    refine ⟨?_, ?_, ?_, structCopy_sgenVCFull dstBase srcBase x y⟩
    · simp [structCopySpec, structCopyBody, LoopFree]
    · simp [structCopySpec, structCopyBody, TailReturn]
    · simp [structCopySpec, structCopyBody, MustReturn]

def bufferStoreProc (bufBase srcBase : Nat) (x y : Int) : VerifiedProc where
  spec := bufferStoreSpec bufBase srcBase x y
  verifyEnv := bufferStoreVerifyEnv bufBase srcBase x y
  sound := by
    refine ⟨?_, ?_, ?_, bufferStore_sgenVCFull bufBase srcBase x y⟩
    · simp [bufferStoreSpec, bufferStoreBody, LoopFree]
    · simp [bufferStoreSpec, bufferStoreBody, TailReturn]
    · simp [bufferStoreSpec, bufferStoreBody, MustReturn]

def bufferClearProc (bufBase : Nat) : VerifiedProc where
  spec := bufferClearSpec bufBase
  verifyEnv := bufferClearVerifyEnv bufBase
  sound := by
    refine ⟨?_, ?_, ?_, bufferClear_sgenVCFull bufBase⟩
    · simp [bufferClearSpec, bufferClearBody, LoopFree]
    · simp [bufferClearSpec, bufferClearBody, TailReturn]
    · simp [bufferClearSpec, bufferClearBody, MustReturn]

def structUnit (dstBase srcBase : Nat) (x y : Int) : VSU where
  name := "struct_unit"
  imports := ["memcpy"]
  exports := [structCopyProc dstBase srcBase x y]
  exports_nodup := by simp [procNames, structCopyProc]

def bufferStoreUnit (bufBase srcBase : Nat) (x y : Int) : VSU where
  name := "buffer_store_unit"
  imports := ["struct_copy"]
  exports := [bufferStoreProc bufBase srcBase x y]
  exports_nodup := by simp [procNames, bufferStoreProc]

def bufferClearUnit (bufBase : Nat) : VSU where
  name := "buffer_clear_unit"
  imports := ["memset"]
  exports := [bufferClearProc bufBase]
  exports_nodup := by simp [procNames, bufferClearProc]

theorem struct_buffer_link_ok (bufBase srcBase : Nat) (x y : Int) :
    ∃ u, link (structUnit bufBase srcBase x y) (bufferStoreUnit bufBase srcBase x y) = some u := by
  refine ⟨compose (structUnit bufBase srcBase x y) (bufferStoreUnit bufBase srcBase x y) ?_, ?_⟩
  · intro name hleft hright
    simp [structUnit, bufferStoreUnit, VSU.exportNames, procNames,
      structCopyProc, bufferStoreProc, structCopySpec, bufferStoreSpec] at hleft hright
    subst name
    simp at hright
  · exact link_eq_some

theorem linked_buffer_store_sound (bufBase srcBase : Nat) (x y : Int) :
    ∃ u, link (structUnit bufBase srcBase x y) (bufferStoreUnit bufBase srcBase x y) = some u ∧
      VSU.exportSound u "buffer_store" := by
  rcases struct_buffer_link_ok bufBase srcBase x y with ⟨u, hlink⟩
  refine ⟨u, hlink, ?_⟩
  simpa [bufferStoreSpec] using
    (link_right_export_sound (u1 := structUnit bufBase srcBase x y)
      (u2 := bufferStoreUnit bufBase srcBase x y) (u := u) hlink
      (proc := bufferStoreProc bufBase srcBase x y) (by simp [bufferStoreUnit]))

theorem linked_struct_copy_resolves_buffer_import (bufBase srcBase : Nat) (x y : Int) :
    ∃ u, link (structUnit bufBase srcBase x y) (bufferStoreUnit bufBase srcBase x y) = some u ∧
      "struct_copy" ∉ u.imports := by
  rcases struct_buffer_link_ok bufBase srcBase x y with ⟨u, hlink⟩
  refine ⟨u, hlink, ?_⟩
  exact link_resolves_right_import hlink
    (by simp [bufferStoreUnit])
    (by simp [structUnit, VSU.exportNames, procNames, structCopyProc, structCopySpec])
    (by simp [structUnit])

end HeytingLean.LeanCP.RealWorld
