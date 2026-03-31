import HeytingLean.LeanCP.Lang.CSemanticsDecEq
import HeytingLean.LeanCP.Core.VarLemmas
import HeytingLean.LeanCP.Tactics.Forward

namespace HeytingLean.LeanCP.Examples

open HeytingLean.LeanCP

/-- Three-cell heap layout used by the insertion-sort benchmark. -/
def insertionHeap3 (base : Nat) (x y z : Int) : Heap :=
  (((Heap.empty.write base (.int x)).write (base + 1) (.int y)).write (base + 2) (.int z))

def sort2Lo (x y : Int) : Int :=
  if y < x then y else x

def sort2Hi (x y : Int) : Int :=
  if y < x then x else y

def sort3Lo (x y z : Int) : Int :=
  if z < sort2Lo x y then z else sort2Lo x y

def sort3Mid (x y z : Int) : Int :=
  if z < sort2Hi x y then
    if z < sort2Lo x y then sort2Lo x y else z
  else
    sort2Hi x y

def sort3Hi (x y z : Int) : Int :=
  if z < sort2Hi x y then sort2Hi x y else z

private theorem sort2Lo_le_sort2Hi (x y : Int) : sort2Lo x y ≤ sort2Hi x y := by
  by_cases hxy : y < x
  · simp [sort2Lo, sort2Hi, hxy, le_of_lt hxy]
  · simp [sort2Lo, sort2Hi, hxy, not_lt.mp hxy]

/-- Read-only three-cell array predicate for the benchmark heap surface. -/
def array3At_s (base : Nat) (x y z : Int) : SProp := fun st =>
  st.heap.read base = some (.int x) ∧
  st.heap.read (base + 1) = some (.int y) ∧
  st.heap.read (base + 2) = some (.int z)

def insertionSortInitOf (base : Nat) (x y z : Int) : CState :=
  { heap := insertionHeap3 base x y z
    env := [("a", .ptr 0 (Int.ofNat base)), ("n", .int 3)]
    nextAddr := base + 100 }

def insertionSortAfterInitOf (base : Nat) (x y z : Int) : CState :=
  { heap := insertionHeap3 base x y z
    env := [("i", .int 1), ("a", .ptr 0 (Int.ofNat base)), ("n", .int 3)]
    nextAddr := base + 100 }

def insertionSortAfterKeyOf (base : Nat) (x y z : Int) : CState :=
  (insertionSortAfterInitOf base x y z).updateVar "key" (.int y)

def insertionSortAfterJOf (base : Nat) (x y z : Int) : CState :=
  (insertionSortAfterKeyOf base x y z).updateVar "j" (.int 1)

def insertionSortBeforeInnerOf (base : Nat) (x y z : Int) : CState :=
  (insertionSortAfterJOf base x y z).updateVar "inserted" (.int 0)

def insertionSortAfterShiftWriteOf (base : Nat) (x y z : Int) : CState :=
  (insertionSortBeforeInnerOf base x y z).withHeap
    ((insertionSortBeforeInnerOf base x y z).heap.write (base + 1) (.int x))

def insertionSortAfterShiftOf (base : Nat) (x y z : Int) : CState :=
  (insertionSortAfterShiftWriteOf base x y z).updateVar "j" (.int 0)

def insertionSortAfterNoShiftOf (base : Nat) (x y z : Int) : CState :=
  (insertionSortBeforeInnerOf base x y z).updateVar "inserted" (.int 1)

def insertionSortAfterShiftWritebackOf (base : Nat) (x y z : Int) : CState :=
  (insertionSortAfterShiftOf base x y z).withHeap
    ((insertionSortAfterShiftOf base x y z).heap.write base (.int y))

def insertionSortAfterNoShiftWritebackOf (base : Nat) (x y z : Int) : CState :=
  (insertionSortAfterNoShiftOf base x y z).withHeap
    ((insertionSortAfterNoShiftOf base x y z).heap.write (base + 1) (.int y))

def insertionSortAfterPass1Of (base : Nat) (x y z : Int) : CState :=
  if y < x then
    (insertionSortAfterShiftWritebackOf base x y z).updateVar "i" (.int 2)
  else
    (insertionSortAfterNoShiftWritebackOf base x y z).updateVar "i" (.int 2)

def insertionSortPass2KeyOf (base : Nat) (x y z : Int) : CState :=
  (insertionSortAfterPass1Of base x y z).updateVar "key" (.int z)

def insertionSortPass2AfterJOf (base : Nat) (x y z : Int) : CState :=
  (insertionSortPass2KeyOf base x y z).updateVar "j" (.int 2)

def insertionSortPass2BeforeInnerOf (base : Nat) (x y z : Int) : CState :=
  (insertionSortPass2AfterJOf base x y z).updateVar "inserted" (.int 0)

def insertionSortPass2AfterHiShiftWriteOf (base : Nat) (x y z : Int) : CState :=
  (insertionSortPass2BeforeInnerOf base x y z).withHeap
    ((insertionSortPass2BeforeInnerOf base x y z).heap.write (base + 2) (.int (sort2Hi x y)))

def insertionSortPass2AfterHiShiftOf (base : Nat) (x y z : Int) : CState :=
  (insertionSortPass2AfterHiShiftWriteOf base x y z).updateVar "j" (.int 1)

def insertionSortPass2AfterHiNoShiftOf (base : Nat) (x y z : Int) : CState :=
  (insertionSortPass2BeforeInnerOf base x y z).updateVar "inserted" (.int 1)

def insertionSortPass2AfterMidNoShiftOf (base : Nat) (x y z : Int) : CState :=
  (insertionSortPass2AfterHiShiftOf base x y z).updateVar "inserted" (.int 1)

def insertionSortPass2AfterLoShiftWriteOf (base : Nat) (x y z : Int) : CState :=
  (insertionSortPass2AfterHiShiftOf base x y z).withHeap
    ((insertionSortPass2AfterHiShiftOf base x y z).heap.write (base + 1) (.int (sort2Lo x y)))

def insertionSortPass2AfterLoShiftOf (base : Nat) (x y z : Int) : CState :=
  (insertionSortPass2AfterLoShiftWriteOf base x y z).updateVar "j" (.int 0)

def insertionSortPass2AfterHiWritebackOf (base : Nat) (x y z : Int) : CState :=
  (insertionSortPass2AfterHiNoShiftOf base x y z).withHeap
    ((insertionSortPass2AfterHiNoShiftOf base x y z).heap.write (base + 2) (.int z))

def insertionSortPass2AfterMidWritebackOf (base : Nat) (x y z : Int) : CState :=
  (insertionSortPass2AfterMidNoShiftOf base x y z).withHeap
    ((insertionSortPass2AfterMidNoShiftOf base x y z).heap.write (base + 1) (.int z))

def insertionSortPass2AfterLoWritebackOf (base : Nat) (x y z : Int) : CState :=
  (insertionSortPass2AfterLoShiftOf base x y z).withHeap
    ((insertionSortPass2AfterLoShiftOf base x y z).heap.write base (.int z))

def insertionSortPass2AfterHiOf (base : Nat) (x y z : Int) : CState :=
  (insertionSortPass2AfterHiWritebackOf base x y z).updateVar "i" (.int 3)

def insertionSortPass2AfterMidOf (base : Nat) (x y z : Int) : CState :=
  (insertionSortPass2AfterMidWritebackOf base x y z).updateVar "i" (.int 3)

def insertionSortPass2AfterLoOf (base : Nat) (x y z : Int) : CState :=
  (insertionSortPass2AfterLoWritebackOf base x y z).updateVar "i" (.int 3)

def insertionSortFinalOf (base : Nat) (x y z : Int) : CState :=
  { heap := insertionHeap3 base (sort3Lo x y z) (sort3Mid x y z) (sort3Hi x y z)
    env := [("i", .int 3),
      ("inserted", .int (if z < sort2Hi x y then if z < sort2Lo x y then 0 else 1 else 1)),
      ("j", .int (if z < sort2Hi x y then if z < sort2Lo x y then 0 else 1 else 2)),
      ("key", .int z), ("a", .ptr 0 (Int.ofNat base)), ("n", .int 3)]
    nextAddr := base + 100 }

private theorem insertionHeap3_read_base (base : Nat) (x y z : Int) :
    (insertionHeap3 base x y z).read base = some (.int x) := by
  simp [insertionHeap3]

private theorem insertionHeap3_read_base_add1 (base : Nat) (x y z : Int) :
    (insertionHeap3 base x y z).read (base + 1) = some (.int y) := by
  simp [insertionHeap3]

private theorem insertionHeap3_read_base_add2 (base : Nat) (x y z : Int) :
    (insertionHeap3 base x y z).read (base + 2) = some (.int z) := by
  simp [insertionHeap3]

/-- Three-element insertion sort with a genuine inner/outer while nest. -/
def insertionInnerCond : CExpr :=
  .binop .lAnd
    (.binop .gt (.var "j") (.intLit 0))
    (.binop .eq (.var "inserted") (.intLit 0))

def insertionInnerBody : CStmt :=
  .ite
    (.binop .lt (.var "key")
      (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1))))
    (.seq
      (.assign
        (.deref (.binop .add (.var "a") (.var "j")))
        (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1))))
      (.assign (.var "j") (.binop .sub (.var "j") (.intLit 1))))
    (.assign (.var "inserted") (.intLit 1))

def insertionOuterBody : CStmt :=
  .seq
    (.assign (.var "key") (.arrayAccess (.var "a") (.var "i")))
    (.seq
      (.assign (.var "j") (.var "i"))
      (.seq
        (.assign (.var "inserted") (.intLit 0))
        (.seq
          (.whileInv insertionInnerCond HProp.htrue insertionInnerBody)
          (.seq
            (.assign (.deref (.binop .add (.var "a") (.var "j"))) (.var "key"))
            (.assign (.var "i") (.binop .add (.var "i") (.intLit 1)))))))

def insertionSortBody : CStmt :=
  .seq
    (.assign (.var "i") (.intLit 1))
    (.seq
      (.whileInv (.binop .lt (.var "i") (.var "n")) HProp.htrue insertionOuterBody)
      (.ret (.arrayAccess (.var "a") (.intLit 0))))

def insertionSortInit : CState :=
  insertionSortInitOf 100 3 1 2

def insertionSortFinal : CState :=
  insertionSortFinalOf 100 3 1 2

def insertionSortAfterInit : CState :=
  insertionSortAfterInitOf 100 3 1 2

def insertionSortAfterPass1 : CState :=
  insertionSortAfterPass1Of 100 3 1 2

theorem insertionSort_seed_executes :
    execStmt 29 (.assign (.var "i") (.intLit 1)) insertionSortInit =
      some (.normal insertionSortAfterInit) := by
  native_decide

theorem insertionSort_seed_executes_of (base : Nat) (x y z : Int) :
    execStmt 29 (.assign (.var "i") (.intLit 1)) (insertionSortInitOf base x y z) =
      some (.normal (insertionSortAfterInitOf base x y z)) := by
  simp [execStmt, insertionSortInitOf, insertionSortAfterInitOf, evalExpr, evalStaticExpr,
    CState.updateVar]

theorem insertionSort_seed_forward_verified_of (base : Nat) (x y z : Int) :
    swp (.assign (.var "i") (.intLit 1))
      (fun _ st => st = insertionSortAfterInitOf base x y z)
      (insertionSortInitOf base x y z) := by
  simp [swp, insertionSortInitOf, insertionSortAfterInitOf, evalExpr, evalStaticExpr,
    CState.updateVar]

theorem insertionSort_assign_key_exec_of (fuel : Nat) (base : Nat) (x y z : Int) :
    execStmt (fuel + 1) (.assign (.var "key") (.arrayAccess (.var "a") (.var "i")))
      (insertionSortAfterInitOf base x y z) =
      some (.normal (insertionSortAfterKeyOf base x y z)) := by
  have ha : (insertionSortAfterInitOf base x y z).lookupVar "a" =
      some (.ptr 0 (Int.ofNat base)) := by
    simp [insertionSortAfterInitOf, CState.lookupVar, List.lookup]
  have hi : (insertionSortAfterInitOf base x y z).lookupVar "i" = some (.int 1) := by
    simp [insertionSortAfterInitOf, CState.lookupVar, List.lookup]
  have hAdd :
      evalBinOp .add (CVal.ptr 0 (Int.ofNat base)) (.int 1) =
        some (CVal.ptr 0 (Int.ofNat (base + 1))) := by
    change
      (if 0 ≤ (1 : Int) then
        some (CVal.ptr 0 (Int.ofNat base + 1))
      else none) =
        some (CVal.ptr 0 (Int.ofNat (base + 1)))
    simp
  have hReadHeap :
      (insertionSortAfterInitOf base x y z).heap.read (base + 1) = some (.int y) := by
    simp [insertionSortAfterInitOf, insertionHeap3]
  have hReadPtr :
      (insertionSortAfterInitOf base x y z).readPtr { block := 0, offset := Int.ofNat (base + 1) } =
        some (.int y) := by
    simpa [hReadHeap] using
      (CState.readPtr_block0 (insertionSortAfterInitOf base x y z) (base + 1) (base + 1))
  have hEvalKey :
      evalExpr (.arrayAccess (.var "a") (.var "i")) (insertionSortAfterInitOf base x y z) =
        some (.int y) := by
    simp only [evalExpr, evalStaticExpr, ha, hi, hAdd, Option.bind, Bind.bind]; exact hReadPtr
  simp [execStmt, insertionSortAfterKeyOf, hEvalKey, CState.updateVar]

theorem insertionSort_assign_j_exec_of (fuel : Nat) (base : Nat) (x y z : Int) :
    execStmt (fuel + 1) (.assign (.var "j") (.var "i")) (insertionSortAfterKeyOf base x y z) =
      some (.normal (insertionSortAfterJOf base x y z)) := by
  have hi : (insertionSortAfterKeyOf base x y z).lookupVar "i" = some (.int 1) := by
    simp [insertionSortAfterKeyOf, insertionSortAfterInitOf, CState.lookupVar, CState.updateVar, List.lookup]
  change
    ((insertionSortAfterKeyOf base x y z).lookupVar "i").bind
      (fun v => some (ExecResult.normal ((insertionSortAfterKeyOf base x y z).updateVar "j" v))) =
      some (ExecResult.normal ((insertionSortAfterKeyOf base x y z).updateVar "j" (.int 1)))
  rw [hi]
  rfl

theorem insertionSort_assign_inserted_exec_of (fuel : Nat) (base : Nat) (x y z : Int) :
    execStmt (fuel + 1) (.assign (.var "inserted") (.intLit 0)) (insertionSortAfterJOf base x y z) =
      some (.normal (insertionSortBeforeInnerOf base x y z)) := by
  simp [execStmt, insertionSortAfterJOf, insertionSortBeforeInnerOf, insertionSortAfterKeyOf,
    insertionSortAfterInitOf, evalExpr, evalStaticExpr, insertionHeap3, CState.updateVar]

def insertionSortPrefixBody : CStmt :=
  .seq
    (.assign (.var "key") (.arrayAccess (.var "a") (.var "i")))
    (.seq
      (.assign (.var "j") (.var "i"))
      (.assign (.var "inserted") (.intLit 0)))

def insertionSortSuffixBody : CStmt :=
  .seq
    (.whileInv insertionInnerCond HProp.htrue insertionInnerBody)
    (.seq
      (.assign (.deref (.binop .add (.var "a") (.var "j"))) (.var "key"))
      (.assign (.var "i") (.binop .add (.var "i") (.intLit 1))))

private theorem insertionSortBeforeInner_lookup_a (base : Nat) (x y z : Int) :
    (insertionSortBeforeInnerOf base x y z).lookupVar "a" =
      some (.ptr 0 (Int.ofNat base)) := by
  simp [insertionSortBeforeInnerOf, insertionSortAfterJOf, insertionSortAfterKeyOf,
    insertionSortAfterInitOf, CState.lookupVar, CState.updateVar, List.lookup]

private theorem insertionSortBeforeInner_lookup_j (base : Nat) (x y z : Int) :
    (insertionSortBeforeInnerOf base x y z).lookupVar "j" = some (.int 1) := by
  simp [insertionSortBeforeInnerOf, insertionSortAfterJOf, insertionSortAfterKeyOf,
    insertionSortAfterInitOf, CState.lookupVar, CState.updateVar, List.lookup]

private theorem insertionSortBeforeInner_lookup_key (base : Nat) (x y z : Int) :
    (insertionSortBeforeInnerOf base x y z).lookupVar "key" = some (.int y) := by
  simp [insertionSortBeforeInnerOf, insertionSortAfterJOf, insertionSortAfterKeyOf,
    insertionSortAfterInitOf, CState.lookupVar, CState.updateVar, List.lookup]

private theorem insertionSortBeforeInner_lookup_i (base : Nat) (x y z : Int) :
    (insertionSortBeforeInnerOf base x y z).lookupVar "i" = some (.int 1) := by
  calc
    (insertionSortBeforeInnerOf base x y z).lookupVar "i"
        = (insertionSortAfterJOf base x y z).lookupVar "i" := by
            simpa [insertionSortBeforeInnerOf] using
              (lookupVar_updateVar_ne (insertionSortAfterJOf base x y z) "inserted" "i" (.int 0)
                (by decide : "i" ≠ "inserted"))
    _ = (insertionSortAfterKeyOf base x y z).lookupVar "i" := by
            simpa [insertionSortAfterJOf] using
              (lookupVar_updateVar_ne (insertionSortAfterKeyOf base x y z) "j" "i" (.int 1)
                (by decide : "i" ≠ "j"))
    _ = (insertionSortAfterInitOf base x y z).lookupVar "i" := by
            simpa [insertionSortAfterKeyOf] using
              (lookupVar_updateVar_ne (insertionSortAfterInitOf base x y z) "key" "i" (.int y)
                (by decide : "i" ≠ "key"))
    _ = some (.int 1) := by
            simp [insertionSortAfterInitOf, CState.lookupVar]

private theorem insertionSortBeforeInner_eval_prev (base : Nat) (x y z : Int) :
    evalExpr (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1)))
      (insertionSortBeforeInnerOf base x y z) = some (.int x) := by
  have ha := insertionSortBeforeInner_lookup_a base x y z
  have hj := insertionSortBeforeInner_lookup_j base x y z
  have hSub : evalBinOp .sub (.int 1) (.int 1) = some (.int 0) := by
    native_decide
  have hAdd :
      evalBinOp .add (.ptr 0 (Int.ofNat base)) (.int 0) =
        some (CVal.ptr 0 (Int.ofNat base)) := by
    change
      (if 0 ≤ (0 : Int) then
        some (CVal.ptr 0 (Int.ofNat base + 0))
      else none) = some (CVal.ptr 0 (Int.ofNat base))
    simp
  have hReadHeap :
      (insertionSortBeforeInnerOf base x y z).heap.read base = some (.int x) := by
    simp [insertionSortBeforeInnerOf, insertionSortAfterJOf, insertionSortAfterKeyOf,
      insertionSortAfterInitOf, insertionHeap3, CState.updateVar]
  have hReadPtr :
      (insertionSortBeforeInnerOf base x y z).readPtr { block := 0, offset := Int.ofNat base } =
        some (.int x) := by
    simpa [hReadHeap] using
      (CState.readPtr_block0 (insertionSortBeforeInnerOf base x y z) base base)
  simp only [evalExpr, evalStaticExpr, ha, hj, hSub, hAdd, Option.bind, Bind.bind]; exact hReadPtr

private theorem insertionSortBeforeInner_eval_shift_target (base : Nat) (x y z : Int) :
    evalExpr (.binop .add (.var "a") (.var "j")) (insertionSortBeforeInnerOf base x y z) =
      some (CVal.ptr 0 (Int.ofNat (base + 1))) := by
  have ha := insertionSortBeforeInner_lookup_a base x y z
  have hj := insertionSortBeforeInner_lookup_j base x y z
  have hAdd :
      evalBinOp .add (.ptr 0 (Int.ofNat base)) (.int 1) =
        some (CVal.ptr 0 (Int.ofNat (base + 1))) := by
    change
      (if 0 ≤ (1 : Int) then
        some (CVal.ptr 0 (Int.ofNat base + 1))
      else none) = some (CVal.ptr 0 (Int.ofNat (base + 1)))
    simp
  simp only [evalExpr, evalStaticExpr, ha, hj, hAdd, Option.bind, Bind.bind]

private theorem insertionSortBeforeInner_eval_branch_cond (base : Nat) (x y z : Int) :
    evalExpr
      (.binop .lt (.var "key")
        (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1))))
      (insertionSortBeforeInnerOf base x y z) =
      some (.int (if y < x then 1 else 0)) := by
  simpa [evalExpr, evalStaticExpr, insertionSortBeforeInner_lookup_key base x y z,
    insertionSortBeforeInner_eval_prev base x y z]

private theorem insertionSortBeforeInner_eval_loop_cond (base : Nat) (x y z : Int) :
    evalExpr insertionInnerCond (insertionSortBeforeInnerOf base x y z) = some (.int 1) := by
  have hInserted :
      (insertionSortBeforeInnerOf base x y z).lookupVar "inserted" = some (.int 0) := by
    simpa [insertionSortBeforeInnerOf] using
      (lookupVar_updateVar_eq (insertionSortAfterJOf base x y z) "inserted" (.int 0))
  simp [insertionInnerCond, evalExpr, evalStaticExpr,
    insertionSortBeforeInner_lookup_j base x y z, hInserted, isTruthy]

theorem insertionSort_set_inserted_exec_of (fuel : Nat) (base : Nat) (x y z : Int) :
    execStmt (fuel + 1) (.assign (.var "inserted") (.intLit 1))
      (insertionSortBeforeInnerOf base x y z) =
      some (.normal (insertionSortAfterNoShiftOf base x y z)) := by
  simp [execStmt, insertionSortAfterNoShiftOf, insertionSortBeforeInnerOf, insertionSortAfterJOf,
    insertionSortAfterKeyOf, insertionSortAfterInitOf, evalExpr, evalStaticExpr, CState.updateVar]

theorem insertionSort_shift_write_exec_of (fuel : Nat) (base : Nat) (x y z : Int) :
    execStmt (fuel + 1)
      (.assign
        (.deref (.binop .add (.var "a") (.var "j")))
        (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1))))
      (insertionSortBeforeInnerOf base x y z) =
      some (.normal (insertionSortAfterShiftWriteOf base x y z)) := by
  have hRhs := insertionSortBeforeInner_eval_prev base x y z
  have hPtr := insertionSortBeforeInner_eval_shift_target base x y z
  let st1 := insertionSortBeforeInnerOf base x y z
  let st2 := st1.withHeap (st1.heap.write (base + 1) (.int x))
  have hSt2 : st2 = insertionSortAfterShiftWriteOf base x y z := by
    simp [st2, st1, insertionSortAfterShiftWriteOf]
  have hWrite :
      st1.writePtr { block := 0, offset := Int.ofNat (base + 1) } (.int x) =
        some (insertionSortAfterShiftWriteOf base x y z) := by
    calc
      st1.writePtr { block := 0, offset := Int.ofNat (base + 1) } (.int x)
          = some st2 := by
              simpa [st1, st2] using
                (CState.writePtr_block0 st1 (base + 1) (base + 1) (.int x))
      _ = some (insertionSortAfterShiftWriteOf base x y z) := by simp [hSt2]
  change
    (evalExpr (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1)))
        (insertionSortBeforeInnerOf base x y z)).bind
      (fun v =>
        match evalExpr (.binop .add (.var "a") (.var "j")) (insertionSortBeforeInnerOf base x y z) with
        | some (.ptr block offset) =>
            ExecResult.normal <$> (insertionSortBeforeInnerOf base x y z).writePtr { block := block, offset := offset } v
        | _ => none) =
      some (.normal (insertionSortAfterShiftWriteOf base x y z))
  rw [hRhs, hPtr]
  simpa using congrArg (Option.map ExecResult.normal) hWrite

theorem insertionSort_shift_dec_j_exec_of (fuel : Nat) (base : Nat) (x y z : Int) :
    execStmt (fuel + 1) (.assign (.var "j") (.binop .sub (.var "j") (.intLit 1)))
      (insertionSortAfterShiftWriteOf base x y z) =
      some (.normal (insertionSortAfterShiftOf base x y z)) := by
  have hj :
      (insertionSortAfterShiftWriteOf base x y z).lookupVar "j" = some (.int 1) := by
    calc
      (insertionSortAfterShiftWriteOf base x y z).lookupVar "j"
          = (insertionSortBeforeInnerOf base x y z).lookupVar "j" := by
              simp [insertionSortAfterShiftWriteOf, CState.lookupVar]
      _ = some (.int 1) := insertionSortBeforeInner_lookup_j base x y z
  have hSub :
      evalBinOp .sub (.int 1) (.int 1) = some (.int 0) := by
    native_decide
  change
    (((insertionSortAfterShiftWriteOf base x y z).lookupVar "j").bind
      (fun v1 =>
        evalBinOp .sub v1 (.int 1))).bind
      (fun v =>
        some (ExecResult.normal ((insertionSortAfterShiftWriteOf base x y z).updateVar "j" v))) =
      some (ExecResult.normal (insertionSortAfterShiftOf base x y z))
  rw [hj]
  simpa [hSub, insertionSortAfterShiftOf]

theorem insertionSort_innerBody_lt_exec_of (fuel : Nat) (base : Nat) (x y z : Int) (hxy : y < x) :
    execStmt (fuel + 3) insertionInnerBody (insertionSortBeforeInnerOf base x y z) =
      some (.normal (insertionSortAfterShiftOf base x y z)) := by
  have hCond := insertionSortBeforeInner_eval_branch_cond base x y z
  have hTrue : isTruthy (.int (if y < x then 1 else 0)) = true := by
    simp [hxy, isTruthy]
  have hIte :
      execStmt (fuel + 3) insertionInnerBody (insertionSortBeforeInnerOf base x y z) =
        execStmt (fuel + 2)
          (.seq
            (.assign
              (.deref (.binop .add (.var "a") (.var "j")))
              (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1))))
            (.assign (.var "j") (.binop .sub (.var "j") (.intLit 1))))
          (insertionSortBeforeInnerOf base x y z) := by
    simpa [insertionInnerBody] using
      (execStmt_ite_of_eval_true (fuel := fuel + 2)
        (cond := (.binop .lt (.var "key")
          (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1)))))
        (th := (.seq
          (.assign
            (.deref (.binop .add (.var "a") (.var "j")))
            (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1))))
          (.assign (.var "j") (.binop .sub (.var "j") (.intLit 1)))))
        (el := (.assign (.var "inserted") (.intLit 1)))
        (st := insertionSortBeforeInnerOf base x y z)
        (v := .int (if y < x then 1 else 0))
        hCond hTrue)
  rw [hIte]
  rw [execStmt_seq_of_normal (fuel := fuel + 1)
        (s1 := (.assign
          (.deref (.binop .add (.var "a") (.var "j")))
          (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1)))))
        (s2 := (.assign (.var "j") (.binop .sub (.var "j") (.intLit 1))))
        (st := insertionSortBeforeInnerOf base x y z)
        (st' := insertionSortAfterShiftWriteOf base x y z)
        (h := insertionSort_shift_write_exec_of (fuel + 1) base x y z)]
  simpa using insertionSort_shift_dec_j_exec_of fuel base x y z

theorem insertionSort_innerBody_ge_exec_of (fuel : Nat) (base : Nat) (x y z : Int) (hxy : ¬ y < x) :
    execStmt (fuel + 3) insertionInnerBody (insertionSortBeforeInnerOf base x y z) =
      some (.normal (insertionSortAfterNoShiftOf base x y z)) := by
  have hCond := insertionSortBeforeInner_eval_branch_cond base x y z
  have hFalse : isTruthy (.int (if y < x then 1 else 0)) = false := by
    simp [hxy, isTruthy]
  have hIte :
      execStmt (fuel + 3) insertionInnerBody (insertionSortBeforeInnerOf base x y z) =
        execStmt (fuel + 2) (.assign (.var "inserted") (.intLit 1))
          (insertionSortBeforeInnerOf base x y z) := by
    simpa [insertionInnerBody] using
      (execStmt_ite_of_eval_false (fuel := fuel + 2)
        (cond := (.binop .lt (.var "key")
          (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1)))))
        (th := (.seq
          (.assign
            (.deref (.binop .add (.var "a") (.var "j")))
            (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1))))
          (.assign (.var "j") (.binop .sub (.var "j") (.intLit 1)))))
        (el := (.assign (.var "inserted") (.intLit 1)))
        (st := insertionSortBeforeInnerOf base x y z)
        (v := .int (if y < x then 1 else 0))
        hCond hFalse)
  rw [hIte]
  simpa using insertionSort_set_inserted_exec_of (fuel + 1) base x y z

private theorem insertionSortAfterShift_lookup_a (base : Nat) (x y z : Int) :
    (insertionSortAfterShiftOf base x y z).lookupVar "a" = some (.ptr 0 (Int.ofNat base)) := by
  calc
    (insertionSortAfterShiftOf base x y z).lookupVar "a"
        = (insertionSortAfterShiftWriteOf base x y z).lookupVar "a" := by
            simpa [insertionSortAfterShiftOf] using
              (lookupVar_updateVar_ne (insertionSortAfterShiftWriteOf base x y z) "j" "a" (.int 0)
                (by decide : "a" ≠ "j"))
    _ = (insertionSortBeforeInnerOf base x y z).lookupVar "a" := by
            simp [insertionSortAfterShiftWriteOf, CState.lookupVar]
    _ = some (.ptr 0 (Int.ofNat base)) := insertionSortBeforeInner_lookup_a base x y z

private theorem insertionSortAfterShift_lookup_j (base : Nat) (x y z : Int) :
    (insertionSortAfterShiftOf base x y z).lookupVar "j" = some (.int 0) := by
  simpa [insertionSortAfterShiftOf] using
    (lookupVar_updateVar_eq (insertionSortAfterShiftWriteOf base x y z) "j" (.int 0))

private theorem insertionSortAfterShift_lookup_key (base : Nat) (x y z : Int) :
    (insertionSortAfterShiftOf base x y z).lookupVar "key" = some (.int y) := by
  calc
    (insertionSortAfterShiftOf base x y z).lookupVar "key"
        = (insertionSortAfterShiftWriteOf base x y z).lookupVar "key" := by
            simpa [insertionSortAfterShiftOf] using
              (lookupVar_updateVar_ne (insertionSortAfterShiftWriteOf base x y z) "j" "key" (.int 0)
                (by decide : "key" ≠ "j"))
    _ = (insertionSortBeforeInnerOf base x y z).lookupVar "key" := by
            simp [insertionSortAfterShiftWriteOf, CState.lookupVar]
    _ = some (.int y) := insertionSortBeforeInner_lookup_key base x y z

private theorem insertionSortAfterShift_lookup_i (base : Nat) (x y z : Int) :
    (insertionSortAfterShiftOf base x y z).lookupVar "i" = some (.int 1) := by
  calc
    (insertionSortAfterShiftOf base x y z).lookupVar "i"
        = (insertionSortAfterShiftWriteOf base x y z).lookupVar "i" := by
            simpa [insertionSortAfterShiftOf] using
              (lookupVar_updateVar_ne (insertionSortAfterShiftWriteOf base x y z) "j" "i" (.int 0)
                (by decide : "i" ≠ "j"))
    _ = some (.int 1) := by
          simp [insertionSortAfterShiftWriteOf]
          exact insertionSortBeforeInner_lookup_i base x y z

private theorem insertionSortAfterShift_eval_writeback_target (base : Nat) (x y z : Int) :
    evalExpr (.binop .add (.var "a") (.var "j")) (insertionSortAfterShiftOf base x y z) =
      some (CVal.ptr 0 (Int.ofNat base)) := by
  have ha := insertionSortAfterShift_lookup_a base x y z
  have hj := insertionSortAfterShift_lookup_j base x y z
  have hAdd :
      evalBinOp .add (.ptr 0 (Int.ofNat base)) (.int 0) =
        some (CVal.ptr 0 (Int.ofNat base)) := by
    change
      (if 0 ≤ (0 : Int) then
        some (CVal.ptr 0 (Int.ofNat base + 0))
      else none) = some (CVal.ptr 0 (Int.ofNat base))
    simp
  simp only [evalExpr, evalStaticExpr, ha, hj, hAdd, Option.bind, Bind.bind]

private theorem insertionSortAfterShift_eval_loop_cond (base : Nat) (x y z : Int) :
    evalExpr insertionInnerCond (insertionSortAfterShiftOf base x y z) = some (.int 0) := by
  have hInserted :
      (insertionSortAfterShiftOf base x y z).lookupVar "inserted" = some (.int 0) := by
    calc
      (insertionSortAfterShiftOf base x y z).lookupVar "inserted"
          = (insertionSortAfterShiftWriteOf base x y z).lookupVar "inserted" := by
              simpa [insertionSortAfterShiftOf] using
                (lookupVar_updateVar_ne (insertionSortAfterShiftWriteOf base x y z) "j" "inserted" (.int 0)
                  (by decide : "inserted" ≠ "j"))
      _ = (insertionSortBeforeInnerOf base x y z).lookupVar "inserted" := by
              simp [insertionSortAfterShiftWriteOf, CState.lookupVar]
      _ = some (.int 0) := by
              simpa [insertionSortBeforeInnerOf] using
                (lookupVar_updateVar_eq (insertionSortAfterJOf base x y z) "inserted" (.int 0))
  simp [insertionInnerCond, evalExpr, evalStaticExpr,
    insertionSortAfterShift_lookup_j base x y z, hInserted, isTruthy]

theorem insertionSort_shift_writeback_exec_of (fuel : Nat) (base : Nat) (x y z : Int) :
    execStmt (fuel + 1) (.assign (.deref (.binop .add (.var "a") (.var "j"))) (.var "key"))
      (insertionSortAfterShiftOf base x y z) =
      some (.normal (insertionSortAfterShiftWritebackOf base x y z)) := by
  have hKey := insertionSortAfterShift_lookup_key base x y z
  have hPtr := insertionSortAfterShift_eval_writeback_target base x y z
  let st1 := insertionSortAfterShiftOf base x y z
  let st2 := insertionSortAfterShiftWritebackOf base x y z
  have hWrite :
      st1.writePtr { block := 0, offset := Int.ofNat base } (.int y) = some st2 := by
    simpa [st1, st2, insertionSortAfterShiftWritebackOf] using
      (CState.writePtr_block0 st1 base base (.int y))
  change
    (evalExpr (.var "key") (insertionSortAfterShiftOf base x y z)).bind
      (fun v =>
        match evalExpr (.binop .add (.var "a") (.var "j")) (insertionSortAfterShiftOf base x y z) with
        | some (.ptr block offset) =>
            ExecResult.normal <$> (insertionSortAfterShiftOf base x y z).writePtr { block := block, offset := offset } v
        | _ => none) =
      some (.normal (insertionSortAfterShiftWritebackOf base x y z))
  rw [show evalExpr (.var "key") (insertionSortAfterShiftOf base x y z) = some (.int y) by simp only [evalExpr, Option.bind, Bind.bind]; exact hKey, hPtr]
  simpa using congrArg (Option.map ExecResult.normal) hWrite

private theorem insertionSortAfterNoShift_lookup_a (base : Nat) (x y z : Int) :
    (insertionSortAfterNoShiftOf base x y z).lookupVar "a" = some (.ptr 0 (Int.ofNat base)) := by
  calc
    (insertionSortAfterNoShiftOf base x y z).lookupVar "a"
        = (insertionSortBeforeInnerOf base x y z).lookupVar "a" := by
            simpa [insertionSortAfterNoShiftOf] using
              (lookupVar_updateVar_ne (insertionSortBeforeInnerOf base x y z) "inserted" "a" (.int 1)
                (by decide : "a" ≠ "inserted"))
    _ = some (.ptr 0 (Int.ofNat base)) := insertionSortBeforeInner_lookup_a base x y z

private theorem insertionSortAfterNoShift_lookup_j (base : Nat) (x y z : Int) :
    (insertionSortAfterNoShiftOf base x y z).lookupVar "j" = some (.int 1) := by
  calc
    (insertionSortAfterNoShiftOf base x y z).lookupVar "j"
        = (insertionSortBeforeInnerOf base x y z).lookupVar "j" := by
            simpa [insertionSortAfterNoShiftOf] using
              (lookupVar_updateVar_ne (insertionSortBeforeInnerOf base x y z) "inserted" "j" (.int 1)
                (by decide : "j" ≠ "inserted"))
    _ = some (.int 1) := insertionSortBeforeInner_lookup_j base x y z

private theorem insertionSortAfterNoShift_lookup_key (base : Nat) (x y z : Int) :
    (insertionSortAfterNoShiftOf base x y z).lookupVar "key" = some (.int y) := by
  calc
    (insertionSortAfterNoShiftOf base x y z).lookupVar "key"
        = (insertionSortBeforeInnerOf base x y z).lookupVar "key" := by
            simpa [insertionSortAfterNoShiftOf] using
              (lookupVar_updateVar_ne (insertionSortBeforeInnerOf base x y z) "inserted" "key" (.int 1)
                (by decide : "key" ≠ "inserted"))
    _ = some (.int y) := insertionSortBeforeInner_lookup_key base x y z

private theorem insertionSortAfterNoShift_lookup_i (base : Nat) (x y z : Int) :
    (insertionSortAfterNoShiftOf base x y z).lookupVar "i" = some (.int 1) := by
  calc
    (insertionSortAfterNoShiftOf base x y z).lookupVar "i"
        = (insertionSortBeforeInnerOf base x y z).lookupVar "i" := by
            simpa [insertionSortAfterNoShiftOf] using
              (lookupVar_updateVar_ne (insertionSortBeforeInnerOf base x y z) "inserted" "i" (.int 1)
                (by decide : "i" ≠ "inserted"))
    _ = some (.int 1) := insertionSortBeforeInner_lookup_i base x y z

private theorem insertionSortAfterNoShift_eval_writeback_target (base : Nat) (x y z : Int) :
    evalExpr (.binop .add (.var "a") (.var "j")) (insertionSortAfterNoShiftOf base x y z) =
      some (CVal.ptr 0 (Int.ofNat (base + 1))) := by
  have ha := insertionSortAfterNoShift_lookup_a base x y z
  have hj := insertionSortAfterNoShift_lookup_j base x y z
  have hAdd :
      evalBinOp .add (.ptr 0 (Int.ofNat base)) (.int 1) =
        some (CVal.ptr 0 (Int.ofNat (base + 1))) := by
    change
      (if 0 ≤ (1 : Int) then
        some (CVal.ptr 0 (Int.ofNat base + 1))
      else none) = some (CVal.ptr 0 (Int.ofNat (base + 1)))
    simp
  simp only [evalExpr, evalStaticExpr, ha, hj, hAdd, Option.bind, Bind.bind]

private theorem insertionSortAfterNoShift_eval_loop_cond (base : Nat) (x y z : Int) :
    evalExpr insertionInnerCond (insertionSortAfterNoShiftOf base x y z) = some (.int 0) := by
  have hInserted :
      (insertionSortAfterNoShiftOf base x y z).lookupVar "inserted" = some (.int 1) := by
    simpa [insertionSortAfterNoShiftOf] using
      (lookupVar_updateVar_eq (insertionSortBeforeInnerOf base x y z) "inserted" (.int 1))
  simp [insertionInnerCond, evalExpr, evalStaticExpr,
    insertionSortAfterNoShift_lookup_j base x y z, hInserted, isTruthy]

theorem insertionSort_noShift_writeback_exec_of (fuel : Nat) (base : Nat) (x y z : Int) :
    execStmt (fuel + 1) (.assign (.deref (.binop .add (.var "a") (.var "j"))) (.var "key"))
      (insertionSortAfterNoShiftOf base x y z) =
      some (.normal (insertionSortAfterNoShiftWritebackOf base x y z)) := by
  have hKey := insertionSortAfterNoShift_lookup_key base x y z
  have hPtr := insertionSortAfterNoShift_eval_writeback_target base x y z
  let st1 := insertionSortAfterNoShiftOf base x y z
  let st2 := insertionSortAfterNoShiftWritebackOf base x y z
  have hWrite :
      st1.writePtr { block := 0, offset := Int.ofNat (base + 1) } (.int y) = some st2 := by
    simpa [st1, st2, insertionSortAfterNoShiftWritebackOf] using
      (CState.writePtr_block0 st1 (base + 1) (base + 1) (.int y))
  change
    (evalExpr (.var "key") (insertionSortAfterNoShiftOf base x y z)).bind
      (fun v =>
        match evalExpr (.binop .add (.var "a") (.var "j")) (insertionSortAfterNoShiftOf base x y z) with
        | some (.ptr block offset) =>
            ExecResult.normal <$> (insertionSortAfterNoShiftOf base x y z).writePtr { block := block, offset := offset } v
        | _ => none) =
      some (.normal (insertionSortAfterNoShiftWritebackOf base x y z))
  rw [show evalExpr (.var "key") (insertionSortAfterNoShiftOf base x y z) = some (.int y) by simp only [evalExpr, Option.bind, Bind.bind]; exact hKey, hPtr]
  simpa using congrArg (Option.map ExecResult.normal) hWrite

theorem insertionSort_shift_inc_i_exec_of (fuel : Nat) (base : Nat) (x y z : Int) (hxy : y < x) :
    execStmt (fuel + 1) (.assign (.var "i") (.binop .add (.var "i") (.intLit 1)))
      (insertionSortAfterShiftWritebackOf base x y z) =
      some (.normal (insertionSortAfterPass1Of base x y z)) := by
  have hi : (insertionSortAfterShiftWritebackOf base x y z).lookupVar "i" = some (.int 1) := by
    calc
      (insertionSortAfterShiftWritebackOf base x y z).lookupVar "i"
          = (insertionSortAfterShiftOf base x y z).lookupVar "i" := by
              simp [insertionSortAfterShiftWritebackOf, CState.lookupVar]
      _ = some (.int 1) := insertionSortAfterShift_lookup_i base x y z
  have hAdd : evalBinOp .add (.int 1) (.int 1) = some (.int 2) := by
    native_decide
  change
    (((insertionSortAfterShiftWritebackOf base x y z).lookupVar "i").bind
      (fun v1 => evalBinOp .add v1 (.int 1))).bind
      (fun v =>
        some (ExecResult.normal ((insertionSortAfterShiftWritebackOf base x y z).updateVar "i" v))) =
      some (.normal (insertionSortAfterPass1Of base x y z))
  rw [hi]
  simpa [hAdd, insertionSortAfterPass1Of, hxy]

theorem insertionSort_noShift_inc_i_exec_of (fuel : Nat) (base : Nat) (x y z : Int) (hxy : ¬ y < x) :
    execStmt (fuel + 1) (.assign (.var "i") (.binop .add (.var "i") (.intLit 1)))
      (insertionSortAfterNoShiftWritebackOf base x y z) =
      some (.normal (insertionSortAfterPass1Of base x y z)) := by
  have hi : (insertionSortAfterNoShiftWritebackOf base x y z).lookupVar "i" = some (.int 1) := by
    calc
      (insertionSortAfterNoShiftWritebackOf base x y z).lookupVar "i"
          = (insertionSortAfterNoShiftOf base x y z).lookupVar "i" := by
              simp [insertionSortAfterNoShiftWritebackOf, CState.lookupVar]
      _ = some (.int 1) := insertionSortAfterNoShift_lookup_i base x y z
  have hAdd : evalBinOp .add (.int 1) (.int 1) = some (.int 2) := by
    native_decide
  change
    (((insertionSortAfterNoShiftWritebackOf base x y z).lookupVar "i").bind
      (fun v1 => evalBinOp .add v1 (.int 1))).bind
      (fun v =>
        some (ExecResult.normal ((insertionSortAfterNoShiftWritebackOf base x y z).updateVar "i" v))) =
      some (.normal (insertionSortAfterPass1Of base x y z))
  rw [hi]
  simpa [hAdd, insertionSortAfterPass1Of, hxy]

theorem insertionSort_prefix_exec_of_fuel (fuel : Nat) (base : Nat) (x y z : Int) :
    execStmt (fuel + 3) insertionSortPrefixBody (insertionSortAfterInitOf base x y z) =
      some (.normal (insertionSortBeforeInnerOf base x y z)) := by
  simp [insertionSortPrefixBody, execStmt]
  have hKey :
      ((evalExpr (.arrayAccess (.var "a") (.var "i")) (insertionSortAfterInitOf base x y z)).bind
        fun v => some (ExecResult.normal ((insertionSortAfterInitOf base x y z).updateVar "key" v))) =
        some (ExecResult.normal (insertionSortAfterKeyOf base x y z)) := by
    simpa [execStmt] using insertionSort_assign_key_exec_of fuel base x y z
  rw [hKey]
  simp [execStmt]
  have hJ :
      ((insertionSortAfterKeyOf base x y z).lookupVar "i").bind
        (fun v => some (ExecResult.normal ((insertionSortAfterKeyOf base x y z).updateVar "j" v))) =
        some (ExecResult.normal (insertionSortAfterJOf base x y z)) := by
    simpa [execStmt] using insertionSort_assign_j_exec_of fuel base x y z
  rw [hJ]
  simpa using insertionSort_assign_inserted_exec_of fuel base x y z

theorem insertionSort_prefix_exec_of (base : Nat) (x y z : Int) :
    execStmt 28 insertionSortPrefixBody (insertionSortAfterInitOf base x y z) =
      some (.normal (insertionSortBeforeInnerOf base x y z)) := by
  simpa using insertionSort_prefix_exec_of_fuel 25 base x y z

theorem insertionSort_innerWhile_lt_exec_of (fuel : Nat) (base : Nat) (x y z : Int) (hxy : y < x) :
    execStmt (fuel + 4) (.whileInv insertionInnerCond HProp.htrue insertionInnerBody)
      (insertionSortBeforeInnerOf base x y z) =
      some (.normal (insertionSortAfterShiftOf base x y z)) := by
  rw [execStmt_whileInv_of_eval_true_normal (fuel := fuel + 3)
        (cond := insertionInnerCond) (inv := HProp.htrue) (body := insertionInnerBody)
        (st := insertionSortBeforeInnerOf base x y z)
        (st' := insertionSortAfterShiftOf base x y z)
        (v := .int 1)
        (hEval := insertionSortBeforeInner_eval_loop_cond base x y z)
        (hTruth := by simp [isTruthy])
        (hBody := insertionSort_innerBody_lt_exec_of fuel base x y z hxy)]
  exact execStmt_whileInv_of_eval_false (fuel := fuel + 2) (cond := insertionInnerCond)
    (inv := HProp.htrue) (body := insertionInnerBody) (st := insertionSortAfterShiftOf base x y z)
    (v := .int 0) (hEval := insertionSortAfterShift_eval_loop_cond base x y z)
    (hTruth := by simp [isTruthy])

theorem insertionSort_innerWhile_ge_exec_of (fuel : Nat) (base : Nat) (x y z : Int) (hxy : ¬ y < x) :
    execStmt (fuel + 4) (.whileInv insertionInnerCond HProp.htrue insertionInnerBody)
      (insertionSortBeforeInnerOf base x y z) =
      some (.normal (insertionSortAfterNoShiftOf base x y z)) := by
  rw [execStmt_whileInv_of_eval_true_normal (fuel := fuel + 3)
        (cond := insertionInnerCond) (inv := HProp.htrue) (body := insertionInnerBody)
        (st := insertionSortBeforeInnerOf base x y z)
        (st' := insertionSortAfterNoShiftOf base x y z)
        (v := .int 1)
        (hEval := insertionSortBeforeInner_eval_loop_cond base x y z)
        (hTruth := by simp [isTruthy])
        (hBody := insertionSort_innerBody_ge_exec_of fuel base x y z hxy)]
  exact execStmt_whileInv_of_eval_false (fuel := fuel + 2) (cond := insertionInnerCond)
    (inv := HProp.htrue) (body := insertionInnerBody) (st := insertionSortAfterNoShiftOf base x y z)
    (v := .int 0) (hEval := insertionSortAfterNoShift_eval_loop_cond base x y z)
    (hTruth := by simp [isTruthy])

theorem insertionSort_pass1_lt_exec_of (fuel : Nat) (base : Nat) (x y z : Int) (hxy : y < x) :
    execStmt (fuel + 6) insertionSortSuffixBody (insertionSortBeforeInnerOf base x y z) =
      some (.normal (insertionSortAfterPass1Of base x y z)) := by
  have hSeq :
      execStmt (fuel + 6) insertionSortSuffixBody (insertionSortBeforeInnerOf base x y z) =
        execStmt (fuel + 5)
          (.seq
            (.assign (.deref (.binop .add (.var "a") (.var "j"))) (.var "key"))
            (.assign (.var "i") (.binop .add (.var "i") (.intLit 1))))
          (insertionSortAfterShiftOf base x y z) := by
    simpa [insertionSortSuffixBody] using
      (execStmt_seq_of_normal (fuel := fuel + 5)
        (s1 := (.whileInv insertionInnerCond HProp.htrue insertionInnerBody))
        (s2 := (.seq
          (.assign (.deref (.binop .add (.var "a") (.var "j"))) (.var "key"))
          (.assign (.var "i") (.binop .add (.var "i") (.intLit 1)))))
        (st := insertionSortBeforeInnerOf base x y z)
        (st' := insertionSortAfterShiftOf base x y z)
        (h := insertionSort_innerWhile_lt_exec_of (fuel + 1) base x y z hxy))
  rw [hSeq]
  rw [execStmt_seq_of_normal (fuel := fuel + 4)
        (s1 := (.assign (.deref (.binop .add (.var "a") (.var "j"))) (.var "key")))
        (s2 := (.assign (.var "i") (.binop .add (.var "i") (.intLit 1))))
        (st := insertionSortAfterShiftOf base x y z)
        (st' := insertionSortAfterShiftWritebackOf base x y z)
        (h := insertionSort_shift_writeback_exec_of (fuel + 3) base x y z)]
  simpa using insertionSort_shift_inc_i_exec_of (fuel + 3) base x y z hxy

theorem insertionSort_pass1_ge_exec_of (fuel : Nat) (base : Nat) (x y z : Int) (hxy : ¬ y < x) :
    execStmt (fuel + 6) insertionSortSuffixBody (insertionSortBeforeInnerOf base x y z) =
      some (.normal (insertionSortAfterPass1Of base x y z)) := by
  have hSeq :
      execStmt (fuel + 6) insertionSortSuffixBody (insertionSortBeforeInnerOf base x y z) =
        execStmt (fuel + 5)
          (.seq
            (.assign (.deref (.binop .add (.var "a") (.var "j"))) (.var "key"))
            (.assign (.var "i") (.binop .add (.var "i") (.intLit 1))))
          (insertionSortAfterNoShiftOf base x y z) := by
    simpa [insertionSortSuffixBody] using
      (execStmt_seq_of_normal (fuel := fuel + 5)
        (s1 := (.whileInv insertionInnerCond HProp.htrue insertionInnerBody))
        (s2 := (.seq
          (.assign (.deref (.binop .add (.var "a") (.var "j"))) (.var "key"))
          (.assign (.var "i") (.binop .add (.var "i") (.intLit 1)))))
        (st := insertionSortBeforeInnerOf base x y z)
        (st' := insertionSortAfterNoShiftOf base x y z)
        (h := insertionSort_innerWhile_ge_exec_of (fuel + 1) base x y z hxy))
  rw [hSeq]
  rw [execStmt_seq_of_normal (fuel := fuel + 4)
        (s1 := (.assign (.deref (.binop .add (.var "a") (.var "j"))) (.var "key")))
        (s2 := (.assign (.var "i") (.binop .add (.var "i") (.intLit 1))))
        (st := insertionSortAfterNoShiftOf base x y z)
        (st' := insertionSortAfterNoShiftWritebackOf base x y z)
        (h := insertionSort_noShift_writeback_exec_of (fuel + 3) base x y z)]
  simpa using insertionSort_noShift_inc_i_exec_of (fuel + 3) base x y z hxy

theorem insertionSort_pass1_correct (fuel : Nat) (base : Nat) (x y z : Int) :
    execStmt (fuel + 6) insertionSortSuffixBody (insertionSortBeforeInnerOf base x y z) =
      some (.normal (insertionSortAfterPass1Of base x y z)) := by
  by_cases hxy : y < x
  · simpa using insertionSort_pass1_lt_exec_of fuel base x y z hxy
  · simpa using insertionSort_pass1_ge_exec_of fuel base x y z hxy

private theorem insertionSortAfterPass1_lookup_a (base : Nat) (x y z : Int) :
    (insertionSortAfterPass1Of base x y z).lookupVar "a" = some (.ptr 0 (Int.ofNat base)) := by
  by_cases hxy : y < x
  · calc
      (insertionSortAfterPass1Of base x y z).lookupVar "a"
          = (insertionSortAfterShiftWritebackOf base x y z).lookupVar "a" := by
              simpa [insertionSortAfterPass1Of, hxy] using
                (lookupVar_updateVar_ne (insertionSortAfterShiftWritebackOf base x y z) "i" "a" (.int 2)
                  (by decide : "a" ≠ "i"))
      _ = (insertionSortAfterShiftOf base x y z).lookupVar "a" := by
            simp [insertionSortAfterShiftWritebackOf, CState.lookupVar]
      _ = (insertionSortAfterShiftWriteOf base x y z).lookupVar "a" := by
            simpa [insertionSortAfterShiftOf] using
              (lookupVar_updateVar_ne (insertionSortAfterShiftWriteOf base x y z) "j" "a" (.int 0)
                (by decide : "a" ≠ "j"))
      _ = (insertionSortBeforeInnerOf base x y z).lookupVar "a" := by
            simp [insertionSortAfterShiftWriteOf, CState.lookupVar]
      _ = some (.ptr 0 (Int.ofNat base)) := insertionSortBeforeInner_lookup_a base x y z
  · calc
      (insertionSortAfterPass1Of base x y z).lookupVar "a"
          = (insertionSortAfterNoShiftWritebackOf base x y z).lookupVar "a" := by
              simpa [insertionSortAfterPass1Of, hxy] using
                (lookupVar_updateVar_ne (insertionSortAfterNoShiftWritebackOf base x y z) "i" "a" (.int 2)
                  (by decide : "a" ≠ "i"))
      _ = (insertionSortAfterNoShiftOf base x y z).lookupVar "a" := by
            simp [insertionSortAfterNoShiftWritebackOf, CState.lookupVar]
      _ = (insertionSortBeforeInnerOf base x y z).lookupVar "a" := by
            simpa [insertionSortAfterNoShiftOf] using
              (lookupVar_updateVar_ne (insertionSortBeforeInnerOf base x y z) "inserted" "a" (.int 1)
                (by decide : "a" ≠ "inserted"))
      _ = some (.ptr 0 (Int.ofNat base)) := insertionSortBeforeInner_lookup_a base x y z

private theorem insertionSortAfterPass1_lookup_i (base : Nat) (x y z : Int) :
    (insertionSortAfterPass1Of base x y z).lookupVar "i" = some (.int 2) := by
  by_cases hxy : y < x
  · simp [insertionSortAfterPass1Of, hxy, insertionSortAfterShiftWritebackOf, insertionSortAfterShiftOf,
      insertionSortAfterShiftWriteOf, insertionSortBeforeInnerOf, insertionSortAfterJOf,
      insertionSortAfterKeyOf, insertionSortAfterInitOf, CState.lookupVar, CState.updateVar, List.lookup]
  · simp [insertionSortAfterPass1Of, hxy, insertionSortAfterNoShiftWritebackOf, insertionSortAfterNoShiftOf,
      insertionSortBeforeInnerOf, insertionSortAfterJOf, insertionSortAfterKeyOf,
      insertionSortAfterInitOf, CState.lookupVar, CState.updateVar, List.lookup]

private theorem insertionSortAfterPass1_read_base (base : Nat) (x y z : Int) :
    (insertionSortAfterPass1Of base x y z).heap.read base = some (.int (sort2Lo x y)) := by
  by_cases hxy : y < x
  · simp [insertionSortAfterPass1Of, hxy, insertionSortAfterShiftWritebackOf, insertionSortAfterShiftOf,
      insertionSortAfterShiftWriteOf, insertionSortBeforeInnerOf, insertionSortAfterJOf,
      insertionSortAfterKeyOf, insertionSortAfterInitOf, insertionHeap3, sort2Lo]
  · simpa [insertionSortAfterPass1Of, hxy, insertionSortAfterNoShiftWritebackOf, insertionSortAfterNoShiftOf,
      insertionSortBeforeInnerOf, insertionSortAfterJOf, insertionSortAfterKeyOf,
      insertionSortAfterInitOf, sort2Lo, hxy] using
        (insertionHeap3_read_base base x y z)

private theorem insertionSortAfterPass1_read_base_add1 (base : Nat) (x y z : Int) :
    (insertionSortAfterPass1Of base x y z).heap.read (base + 1) = some (.int (sort2Hi x y)) := by
  by_cases hxy : y < x
  · simp [insertionSortAfterPass1Of, hxy, insertionSortAfterShiftWritebackOf, insertionSortAfterShiftOf,
      insertionSortAfterShiftWriteOf, insertionSortBeforeInnerOf, insertionSortAfterJOf,
      insertionSortAfterKeyOf, insertionSortAfterInitOf, insertionHeap3, sort2Hi]
  · simp [insertionSortAfterPass1Of, hxy, insertionSortAfterNoShiftWritebackOf, insertionSortAfterNoShiftOf,
      insertionSortBeforeInnerOf, insertionSortAfterJOf, insertionSortAfterKeyOf,
      insertionSortAfterInitOf, insertionHeap3, sort2Hi]

private theorem insertionSortAfterPass1_read_base_add2 (base : Nat) (x y z : Int) :
    (insertionSortAfterPass1Of base x y z).heap.read (base + 2) = some (.int z) := by
  by_cases hxy : y < x
  · have hBefore :
        (insertionSortBeforeInnerOf base x y z).heap.read (base + 2) = some (.int z) := by
      simpa [insertionSortBeforeInnerOf, insertionSortAfterJOf, insertionSortAfterKeyOf,
        insertionSortAfterInitOf] using
        (insertionHeap3_read_base_add2 base x y z)
    calc
      (insertionSortAfterPass1Of base x y z).heap.read (base + 2)
          = (insertionSortAfterShiftWritebackOf base x y z).heap.read (base + 2) := by
              simp [insertionSortAfterPass1Of, hxy, CState.updateVar]
      _ = (insertionSortAfterShiftOf base x y z).heap.read (base + 2) := by
            simp [insertionSortAfterShiftWritebackOf]
      _ = (insertionSortBeforeInnerOf base x y z).heap.read (base + 2) := by
            simp [insertionSortAfterShiftOf, insertionSortAfterShiftWriteOf]
      _ = some (.int z) := hBefore
  · simpa [insertionSortAfterPass1Of, hxy, insertionSortAfterNoShiftWritebackOf, insertionSortAfterNoShiftOf,
      insertionSortBeforeInnerOf, insertionSortAfterJOf, insertionSortAfterKeyOf,
      insertionSortAfterInitOf] using
        (insertionHeap3_read_base_add2 base x y z)

theorem insertionSort_pass2_assign_key_exec_of (fuel : Nat) (base : Nat) (x y z : Int) :
    execStmt (fuel + 1) (.assign (.var "key") (.arrayAccess (.var "a") (.var "i")))
      (insertionSortAfterPass1Of base x y z) =
      some (.normal (insertionSortPass2KeyOf base x y z)) := by
  have ha := insertionSortAfterPass1_lookup_a base x y z
  have hi := insertionSortAfterPass1_lookup_i base x y z
  have hAdd :
      evalBinOp .add (CVal.ptr 0 (Int.ofNat base)) (.int 2) =
        some (CVal.ptr 0 (Int.ofNat (base + 2))) := by
    change
      (if 0 ≤ (2 : Int) then
        some (CVal.ptr 0 (Int.ofNat base + 2))
      else none) = some (CVal.ptr 0 (Int.ofNat (base + 2)))
    simp
  have hReadHeap := insertionSortAfterPass1_read_base_add2 base x y z
  have hReadPtr :
      (insertionSortAfterPass1Of base x y z).readPtr { block := 0, offset := Int.ofNat (base + 2) } =
        some (.int z) := by
    simpa [hReadHeap] using
      (CState.readPtr_block0 (insertionSortAfterPass1Of base x y z) (base + 2) (base + 2))
  have hEvalKey :
      evalExpr (.arrayAccess (.var "a") (.var "i")) (insertionSortAfterPass1Of base x y z) =
        some (.int z) := by
    simp only [evalExpr, evalStaticExpr, ha, hi, hAdd, Option.bind, Bind.bind]; exact hReadPtr
  simp [execStmt, insertionSortPass2KeyOf, hEvalKey, CState.updateVar]

theorem insertionSort_pass2_assign_j_exec_of (fuel : Nat) (base : Nat) (x y z : Int) :
    execStmt (fuel + 1) (.assign (.var "j") (.var "i")) (insertionSortPass2KeyOf base x y z) =
      some (.normal (insertionSortPass2AfterJOf base x y z)) := by
  have hi : (insertionSortPass2KeyOf base x y z).lookupVar "i" = some (.int 2) := by
    calc
      (insertionSortPass2KeyOf base x y z).lookupVar "i"
          = (insertionSortAfterPass1Of base x y z).lookupVar "i" := by
              simpa [insertionSortPass2KeyOf] using
                (lookupVar_updateVar_ne (insertionSortAfterPass1Of base x y z) "key" "i" (.int z)
                  (by decide : "i" ≠ "key"))
      _ = some (.int 2) := insertionSortAfterPass1_lookup_i base x y z
  change
    ((insertionSortPass2KeyOf base x y z).lookupVar "i").bind
      (fun v => some (ExecResult.normal ((insertionSortPass2KeyOf base x y z).updateVar "j" v))) =
      some (ExecResult.normal ((insertionSortPass2KeyOf base x y z).updateVar "j" (.int 2)))
  rw [hi]
  rfl

theorem insertionSort_pass2_assign_inserted_exec_of (fuel : Nat) (base : Nat) (x y z : Int) :
    execStmt (fuel + 1) (.assign (.var "inserted") (.intLit 0)) (insertionSortPass2AfterJOf base x y z) =
      some (.normal (insertionSortPass2BeforeInnerOf base x y z)) := by
  simp [execStmt, insertionSortPass2AfterJOf, insertionSortPass2BeforeInnerOf, insertionSortPass2KeyOf,
    evalExpr, evalStaticExpr, CState.updateVar]

private theorem insertionSortPass2BeforeInner_lookup_a (base : Nat) (x y z : Int) :
    (insertionSortPass2BeforeInnerOf base x y z).lookupVar "a" = some (.ptr 0 (Int.ofNat base)) := by
  calc
    (insertionSortPass2BeforeInnerOf base x y z).lookupVar "a"
        = (insertionSortPass2AfterJOf base x y z).lookupVar "a" := by
            simpa [insertionSortPass2BeforeInnerOf] using
              (lookupVar_updateVar_ne (insertionSortPass2AfterJOf base x y z) "inserted" "a" (.int 0)
                (by decide : "a" ≠ "inserted"))
    _ = (insertionSortPass2KeyOf base x y z).lookupVar "a" := by
            simpa [insertionSortPass2AfterJOf] using
              (lookupVar_updateVar_ne (insertionSortPass2KeyOf base x y z) "j" "a" (.int 2)
                (by decide : "a" ≠ "j"))
    _ = (insertionSortAfterPass1Of base x y z).lookupVar "a" := by
            simpa [insertionSortPass2KeyOf] using
              (lookupVar_updateVar_ne (insertionSortAfterPass1Of base x y z) "key" "a" (.int z)
                (by decide : "a" ≠ "key"))
    _ = some (.ptr 0 (Int.ofNat base)) := insertionSortAfterPass1_lookup_a base x y z

private theorem insertionSortPass2BeforeInner_lookup_j (base : Nat) (x y z : Int) :
    (insertionSortPass2BeforeInnerOf base x y z).lookupVar "j" = some (.int 2) := by
  calc
    (insertionSortPass2BeforeInnerOf base x y z).lookupVar "j"
        = (insertionSortPass2AfterJOf base x y z).lookupVar "j" := by
            simpa [insertionSortPass2BeforeInnerOf] using
              (lookupVar_updateVar_ne (insertionSortPass2AfterJOf base x y z) "inserted" "j" (.int 0)
                (by decide : "j" ≠ "inserted"))
    _ = some (.int 2) := by
            simpa [insertionSortPass2AfterJOf] using
              (lookupVar_updateVar_eq (insertionSortPass2KeyOf base x y z) "j" (.int 2))

private theorem insertionSortPass2BeforeInner_lookup_key (base : Nat) (x y z : Int) :
    (insertionSortPass2BeforeInnerOf base x y z).lookupVar "key" = some (.int z) := by
  calc
    (insertionSortPass2BeforeInnerOf base x y z).lookupVar "key"
        = (insertionSortPass2AfterJOf base x y z).lookupVar "key" := by
            simpa [insertionSortPass2BeforeInnerOf] using
              (lookupVar_updateVar_ne (insertionSortPass2AfterJOf base x y z) "inserted" "key" (.int 0)
                (by decide : "key" ≠ "inserted"))
    _ = (insertionSortPass2KeyOf base x y z).lookupVar "key" := by
            simpa [insertionSortPass2AfterJOf] using
              (lookupVar_updateVar_ne (insertionSortPass2KeyOf base x y z) "j" "key" (.int 2)
                (by decide : "key" ≠ "j"))
    _ = some (.int z) := by
            simpa [insertionSortPass2KeyOf] using
              (lookupVar_updateVar_eq (insertionSortAfterPass1Of base x y z) "key" (.int z))

private theorem insertionSortPass2BeforeInner_lookup_i (base : Nat) (x y z : Int) :
    (insertionSortPass2BeforeInnerOf base x y z).lookupVar "i" = some (.int 2) := by
  calc
    (insertionSortPass2BeforeInnerOf base x y z).lookupVar "i"
        = (insertionSortPass2AfterJOf base x y z).lookupVar "i" := by
            simpa [insertionSortPass2BeforeInnerOf] using
              (lookupVar_updateVar_ne (insertionSortPass2AfterJOf base x y z) "inserted" "i" (.int 0)
                (by decide : "i" ≠ "inserted"))
    _ = (insertionSortPass2KeyOf base x y z).lookupVar "i" := by
            simpa [insertionSortPass2AfterJOf] using
              (lookupVar_updateVar_ne (insertionSortPass2KeyOf base x y z) "j" "i" (.int 2)
                (by decide : "i" ≠ "j"))
    _ = (insertionSortAfterPass1Of base x y z).lookupVar "i" := by
            simpa [insertionSortPass2KeyOf] using
              (lookupVar_updateVar_ne (insertionSortAfterPass1Of base x y z) "key" "i" (.int z)
                (by decide : "i" ≠ "key"))
    _ = some (.int 2) := insertionSortAfterPass1_lookup_i base x y z

private theorem insertionSortPass2BeforeInner_eval_prev_hi (base : Nat) (x y z : Int) :
    evalExpr (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1)))
      (insertionSortPass2BeforeInnerOf base x y z) = some (.int (sort2Hi x y)) := by
  have ha := insertionSortPass2BeforeInner_lookup_a base x y z
  have hj := insertionSortPass2BeforeInner_lookup_j base x y z
  have hSub : evalBinOp .sub (.int 2) (.int 1) = some (.int 1) := by
    native_decide
  have hAdd :
      evalBinOp .add (.ptr 0 (Int.ofNat base)) (.int 1) =
        some (CVal.ptr 0 (Int.ofNat (base + 1))) := by
    change
      (if 0 ≤ (1 : Int) then
        some (CVal.ptr 0 (Int.ofNat base + 1))
      else none) = some (CVal.ptr 0 (Int.ofNat (base + 1)))
    simp
  have hReadHeap := insertionSortAfterPass1_read_base_add1 base x y z
  have hReadHeap' :
      (insertionSortPass2BeforeInnerOf base x y z).heap.read (base + 1) = some (.int (sort2Hi x y)) := by
    simpa [insertionSortPass2BeforeInnerOf, insertionSortPass2AfterJOf, insertionSortPass2KeyOf,
      CState.updateVar] using hReadHeap
  have hReadPtr :
      (insertionSortPass2BeforeInnerOf base x y z).readPtr { block := 0, offset := Int.ofNat (base + 1) } =
        some (.int (sort2Hi x y)) := by
    simpa [hReadHeap'] using
      (CState.readPtr_block0 (insertionSortPass2BeforeInnerOf base x y z) (base + 1) (base + 1))
  simp only [evalExpr, evalStaticExpr, ha, hj, hSub, hAdd, Option.bind, Bind.bind]; exact hReadPtr

private theorem insertionSortPass2BeforeInner_eval_branch_cond (base : Nat) (x y z : Int) :
    evalExpr
      (.binop .lt (.var "key")
        (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1))))
      (insertionSortPass2BeforeInnerOf base x y z) =
      some (.int (if z < sort2Hi x y then 1 else 0)) := by
  simpa [evalExpr, evalStaticExpr, insertionSortPass2BeforeInner_lookup_key base x y z,
    insertionSortPass2BeforeInner_eval_prev_hi base x y z]

private theorem insertionSortPass2BeforeInner_eval_loop_cond (base : Nat) (x y z : Int) :
    evalExpr insertionInnerCond (insertionSortPass2BeforeInnerOf base x y z) = some (.int 1) := by
  have hInserted :
      (insertionSortPass2BeforeInnerOf base x y z).lookupVar "inserted" = some (.int 0) := by
    simpa [insertionSortPass2BeforeInnerOf] using
      (lookupVar_updateVar_eq (insertionSortPass2AfterJOf base x y z) "inserted" (.int 0))
  simp [insertionInnerCond, evalExpr, evalStaticExpr,
    insertionSortPass2BeforeInner_lookup_j base x y z, hInserted, isTruthy]

theorem insertionSort_pass2_set_inserted_exec_of (fuel : Nat) (base : Nat) (x y z : Int) :
    execStmt (fuel + 1) (.assign (.var "inserted") (.intLit 1))
      (insertionSortPass2BeforeInnerOf base x y z) =
      some (.normal (insertionSortPass2AfterHiNoShiftOf base x y z)) := by
  simp [execStmt, insertionSortPass2AfterHiNoShiftOf, insertionSortPass2BeforeInnerOf,
    insertionSortPass2AfterJOf, insertionSortPass2KeyOf, evalExpr, evalStaticExpr, CState.updateVar]

theorem insertionSort_pass2_hi_shift_write_exec_of (fuel : Nat) (base : Nat) (x y z : Int) :
    execStmt (fuel + 1)
      (.assign
        (.deref (.binop .add (.var "a") (.var "j")))
        (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1))))
      (insertionSortPass2BeforeInnerOf base x y z) =
      some (.normal (insertionSortPass2AfterHiShiftWriteOf base x y z)) := by
  have hRhs := insertionSortPass2BeforeInner_eval_prev_hi base x y z
  have ha := insertionSortPass2BeforeInner_lookup_a base x y z
  have hj := insertionSortPass2BeforeInner_lookup_j base x y z
  have hPtr :
      evalExpr (.binop .add (.var "a") (.var "j")) (insertionSortPass2BeforeInnerOf base x y z) =
        some (CVal.ptr 0 (Int.ofNat (base + 2))) := by
    have hAdd :
        evalBinOp .add (.ptr 0 (Int.ofNat base)) (.int 2) =
          some (CVal.ptr 0 (Int.ofNat (base + 2))) := by
      change
        (if 0 ≤ (2 : Int) then
          some (CVal.ptr 0 (Int.ofNat base + 2))
        else none) = some (CVal.ptr 0 (Int.ofNat (base + 2)))
      simp
    simp only [evalExpr, evalStaticExpr, ha, hj, hAdd, Option.bind, Bind.bind]
  let st1 := insertionSortPass2BeforeInnerOf base x y z
  let st2 := insertionSortPass2AfterHiShiftWriteOf base x y z
  have hWrite :
      st1.writePtr { block := 0, offset := Int.ofNat (base + 2) } (.int (sort2Hi x y)) = some st2 := by
    simpa [st1, st2, insertionSortPass2AfterHiShiftWriteOf] using
      (CState.writePtr_block0 st1 (base + 2) (base + 2) (.int (sort2Hi x y)))
  simpa [execStmt, hRhs, hPtr] using congrArg (Option.map ExecResult.normal) hWrite

theorem insertionSort_pass2_hi_shift_dec_j_exec_of (fuel : Nat) (base : Nat) (x y z : Int) :
    execStmt (fuel + 1) (.assign (.var "j") (.binop .sub (.var "j") (.intLit 1)))
      (insertionSortPass2AfterHiShiftWriteOf base x y z) =
      some (.normal (insertionSortPass2AfterHiShiftOf base x y z)) := by
  have hj :
      (insertionSortPass2AfterHiShiftWriteOf base x y z).lookupVar "j" = some (.int 2) := by
    calc
      (insertionSortPass2AfterHiShiftWriteOf base x y z).lookupVar "j"
          = (insertionSortPass2BeforeInnerOf base x y z).lookupVar "j" := by
              simp [insertionSortPass2AfterHiShiftWriteOf, CState.lookupVar]
      _ = some (.int 2) := insertionSortPass2BeforeInner_lookup_j base x y z
  have hSub :
      evalBinOp .sub (.int 2) (.int 1) = some (.int 1) := by
    native_decide
  change
    (((insertionSortPass2AfterHiShiftWriteOf base x y z).lookupVar "j").bind
      (fun v1 => evalBinOp .sub v1 (.int 1))).bind
      (fun v =>
        some (ExecResult.normal ((insertionSortPass2AfterHiShiftWriteOf base x y z).updateVar "j" v))) =
      some (ExecResult.normal (insertionSortPass2AfterHiShiftOf base x y z))
  rw [hj]
  simpa [hSub, insertionSortPass2AfterHiShiftOf]

theorem insertionSort_pass2_innerBody_hi_exec_of (fuel : Nat) (base : Nat) (x y z : Int)
    (hz : ¬ z < sort2Hi x y) :
    execStmt (fuel + 3) insertionInnerBody (insertionSortPass2BeforeInnerOf base x y z) =
      some (.normal (insertionSortPass2AfterHiNoShiftOf base x y z)) := by
  have hCond := insertionSortPass2BeforeInner_eval_branch_cond base x y z
  have hFalse : isTruthy (.int (if z < sort2Hi x y then 1 else 0)) = false := by
    simp [hz, isTruthy]
  have hIte :
      execStmt (fuel + 3) insertionInnerBody (insertionSortPass2BeforeInnerOf base x y z) =
        execStmt (fuel + 2) (.assign (.var "inserted") (.intLit 1))
          (insertionSortPass2BeforeInnerOf base x y z) := by
    simpa [insertionInnerBody] using
      (execStmt_ite_of_eval_false (fuel := fuel + 2)
        (cond := (.binop .lt (.var "key")
          (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1)))))
        (th := (.seq
          (.assign
            (.deref (.binop .add (.var "a") (.var "j")))
            (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1))))
          (.assign (.var "j") (.binop .sub (.var "j") (.intLit 1)))))
        (el := (.assign (.var "inserted") (.intLit 1)))
        (st := insertionSortPass2BeforeInnerOf base x y z)
        (v := .int (if z < sort2Hi x y then 1 else 0))
        hCond hFalse)
  rw [hIte]
  simpa using insertionSort_pass2_set_inserted_exec_of (fuel + 1) base x y z

private theorem insertionSortPass2AfterHiNoShift_lookup_a (base : Nat) (x y z : Int) :
    (insertionSortPass2AfterHiNoShiftOf base x y z).lookupVar "a" = some (.ptr 0 (Int.ofNat base)) := by
  calc
    (insertionSortPass2AfterHiNoShiftOf base x y z).lookupVar "a"
        = (insertionSortPass2BeforeInnerOf base x y z).lookupVar "a" := by
            simpa [insertionSortPass2AfterHiNoShiftOf] using
              (lookupVar_updateVar_ne (insertionSortPass2BeforeInnerOf base x y z) "inserted" "a" (.int 1)
                (by decide : "a" ≠ "inserted"))
    _ = some (.ptr 0 (Int.ofNat base)) := insertionSortPass2BeforeInner_lookup_a base x y z

private theorem insertionSortPass2AfterHiNoShift_lookup_j (base : Nat) (x y z : Int) :
    (insertionSortPass2AfterHiNoShiftOf base x y z).lookupVar "j" = some (.int 2) := by
  calc
    (insertionSortPass2AfterHiNoShiftOf base x y z).lookupVar "j"
        = (insertionSortPass2BeforeInnerOf base x y z).lookupVar "j" := by
            simpa [insertionSortPass2AfterHiNoShiftOf] using
              (lookupVar_updateVar_ne (insertionSortPass2BeforeInnerOf base x y z) "inserted" "j" (.int 1)
                (by decide : "j" ≠ "inserted"))
    _ = some (.int 2) := insertionSortPass2BeforeInner_lookup_j base x y z

private theorem insertionSortPass2AfterHiNoShift_lookup_key (base : Nat) (x y z : Int) :
    (insertionSortPass2AfterHiNoShiftOf base x y z).lookupVar "key" = some (.int z) := by
  calc
    (insertionSortPass2AfterHiNoShiftOf base x y z).lookupVar "key"
        = (insertionSortPass2BeforeInnerOf base x y z).lookupVar "key" := by
            simpa [insertionSortPass2AfterHiNoShiftOf] using
              (lookupVar_updateVar_ne (insertionSortPass2BeforeInnerOf base x y z) "inserted" "key" (.int 1)
                (by decide : "key" ≠ "inserted"))
    _ = some (.int z) := insertionSortPass2BeforeInner_lookup_key base x y z

private theorem insertionSortPass2AfterHiNoShift_lookup_i (base : Nat) (x y z : Int) :
    (insertionSortPass2AfterHiNoShiftOf base x y z).lookupVar "i" = some (.int 2) := by
  calc
    (insertionSortPass2AfterHiNoShiftOf base x y z).lookupVar "i"
        = (insertionSortPass2BeforeInnerOf base x y z).lookupVar "i" := by
            simpa [insertionSortPass2AfterHiNoShiftOf] using
              (lookupVar_updateVar_ne (insertionSortPass2BeforeInnerOf base x y z) "inserted" "i" (.int 1)
                (by decide : "i" ≠ "inserted"))
    _ = some (.int 2) := insertionSortPass2BeforeInner_lookup_i base x y z

private theorem insertionSortPass2AfterHiNoShift_eval_writeback_target (base : Nat) (x y z : Int) :
    evalExpr (.binop .add (.var "a") (.var "j")) (insertionSortPass2AfterHiNoShiftOf base x y z) =
      some (CVal.ptr 0 (Int.ofNat (base + 2))) := by
  have ha := insertionSortPass2AfterHiNoShift_lookup_a base x y z
  have hj := insertionSortPass2AfterHiNoShift_lookup_j base x y z
  have hAdd :
      evalBinOp .add (.ptr 0 (Int.ofNat base)) (.int 2) =
        some (CVal.ptr 0 (Int.ofNat (base + 2))) := by
    change
      (if 0 ≤ (2 : Int) then
        some (CVal.ptr 0 (Int.ofNat base + 2))
      else none) = some (CVal.ptr 0 (Int.ofNat (base + 2)))
    simp
  simp only [evalExpr, evalStaticExpr, ha, hj, hAdd, Option.bind, Bind.bind]

private theorem insertionSortPass2AfterHiNoShift_eval_loop_cond (base : Nat) (x y z : Int) :
    evalExpr insertionInnerCond (insertionSortPass2AfterHiNoShiftOf base x y z) = some (.int 0) := by
  have hInserted :
      (insertionSortPass2AfterHiNoShiftOf base x y z).lookupVar "inserted" = some (.int 1) := by
    simpa [insertionSortPass2AfterHiNoShiftOf] using
      (lookupVar_updateVar_eq (insertionSortPass2BeforeInnerOf base x y z) "inserted" (.int 1))
  simp [insertionInnerCond, evalExpr, evalStaticExpr,
    insertionSortPass2AfterHiNoShift_lookup_j base x y z, hInserted, isTruthy]

theorem insertionSort_pass2_innerWhile_hi_exec_of (fuel : Nat) (base : Nat) (x y z : Int)
    (hz : ¬ z < sort2Hi x y) :
    execStmt (fuel + 4) (.whileInv insertionInnerCond HProp.htrue insertionInnerBody)
      (insertionSortPass2BeforeInnerOf base x y z) =
      some (.normal (insertionSortPass2AfterHiNoShiftOf base x y z)) := by
  rw [execStmt_whileInv_of_eval_true_normal (fuel := fuel + 3)
        (cond := insertionInnerCond) (inv := HProp.htrue) (body := insertionInnerBody)
        (st := insertionSortPass2BeforeInnerOf base x y z)
        (st' := insertionSortPass2AfterHiNoShiftOf base x y z)
        (v := .int 1)
        (hEval := insertionSortPass2BeforeInner_eval_loop_cond base x y z)
        (hTruth := by simp [isTruthy])
        (hBody := insertionSort_pass2_innerBody_hi_exec_of fuel base x y z hz)]
  exact execStmt_whileInv_of_eval_false (fuel := fuel + 2) (cond := insertionInnerCond)
    (inv := HProp.htrue) (body := insertionInnerBody) (st := insertionSortPass2AfterHiNoShiftOf base x y z)
    (v := .int 0) (hEval := insertionSortPass2AfterHiNoShift_eval_loop_cond base x y z)
    (hTruth := by simp [isTruthy])

theorem insertionSort_pass2_hi_writeback_exec_of (fuel : Nat) (base : Nat) (x y z : Int) :
    execStmt (fuel + 1) (.assign (.deref (.binop .add (.var "a") (.var "j"))) (.var "key"))
      (insertionSortPass2AfterHiNoShiftOf base x y z) =
      some (.normal (insertionSortPass2AfterHiWritebackOf base x y z)) := by
  have hKey := insertionSortPass2AfterHiNoShift_lookup_key base x y z
  have hPtr := insertionSortPass2AfterHiNoShift_eval_writeback_target base x y z
  let st1 := insertionSortPass2AfterHiNoShiftOf base x y z
  let st2 := insertionSortPass2AfterHiWritebackOf base x y z
  have hWrite :
      st1.writePtr { block := 0, offset := Int.ofNat (base + 2) } (.int z) = some st2 := by
    simpa [st1, st2, insertionSortPass2AfterHiWritebackOf] using
      (CState.writePtr_block0 st1 (base + 2) (base + 2) (.int z))
  simpa [execStmt, hPtr] using
    (show (evalExpr (.var "key") (insertionSortPass2AfterHiNoShiftOf base x y z)).bind
        (fun v =>
          ExecResult.normal <$> (insertionSortPass2AfterHiNoShiftOf base x y z).writePtr
            { block := 0, offset := Int.ofNat (base + 2) } v) =
      some (.normal (insertionSortPass2AfterHiWritebackOf base x y z)) from by
        rw [show evalExpr (.var "key") (insertionSortPass2AfterHiNoShiftOf base x y z) = some (.int z) by
              simp only [evalExpr, Option.bind, Bind.bind]; exact hKey]
        simpa using congrArg (Option.map ExecResult.normal) hWrite)

theorem insertionSort_pass2_hi_inc_i_exec_of (fuel : Nat) (base : Nat) (x y z : Int) :
    execStmt (fuel + 1) (.assign (.var "i") (.binop .add (.var "i") (.intLit 1)))
      (insertionSortPass2AfterHiWritebackOf base x y z) =
      some (.normal (insertionSortPass2AfterHiOf base x y z)) := by
  have hi : (insertionSortPass2AfterHiWritebackOf base x y z).lookupVar "i" = some (.int 2) := by
    calc
      (insertionSortPass2AfterHiWritebackOf base x y z).lookupVar "i"
          = (insertionSortPass2AfterHiNoShiftOf base x y z).lookupVar "i" := by
              simp [insertionSortPass2AfterHiWritebackOf, CState.lookupVar]
      _ = some (.int 2) := insertionSortPass2AfterHiNoShift_lookup_i base x y z
  have hAdd : evalBinOp .add (.int 2) (.int 1) = some (.int 3) := by
    native_decide
  change
    (((insertionSortPass2AfterHiWritebackOf base x y z).lookupVar "i").bind
      (fun v1 => evalBinOp .add v1 (.int 1))).bind
      (fun v =>
        some (ExecResult.normal ((insertionSortPass2AfterHiWritebackOf base x y z).updateVar "i" v))) =
      some (.normal (insertionSortPass2AfterHiOf base x y z))
  rw [hi]
  simpa [hAdd, insertionSortPass2AfterHiOf]

theorem insertionSort_pass2_hi_exec_of (fuel : Nat) (base : Nat) (x y z : Int)
    (hz : ¬ z < sort2Hi x y) :
    execStmt (fuel + 6) insertionSortSuffixBody (insertionSortPass2BeforeInnerOf base x y z) =
      some (.normal (insertionSortPass2AfterHiOf base x y z)) := by
  have hSeq :
      execStmt (fuel + 6) insertionSortSuffixBody (insertionSortPass2BeforeInnerOf base x y z) =
        execStmt (fuel + 5)
          (.seq
            (.assign (.deref (.binop .add (.var "a") (.var "j"))) (.var "key"))
            (.assign (.var "i") (.binop .add (.var "i") (.intLit 1))))
          (insertionSortPass2AfterHiNoShiftOf base x y z) := by
    simpa [insertionSortSuffixBody] using
      (execStmt_seq_of_normal (fuel := fuel + 5)
        (s1 := (.whileInv insertionInnerCond HProp.htrue insertionInnerBody))
        (s2 := (.seq
          (.assign (.deref (.binop .add (.var "a") (.var "j"))) (.var "key"))
          (.assign (.var "i") (.binop .add (.var "i") (.intLit 1)))))
        (st := insertionSortPass2BeforeInnerOf base x y z)
        (st' := insertionSortPass2AfterHiNoShiftOf base x y z)
        (h := insertionSort_pass2_innerWhile_hi_exec_of (fuel + 1) base x y z hz))
  rw [hSeq]
  rw [execStmt_seq_of_normal (fuel := fuel + 4)
        (s1 := (.assign (.deref (.binop .add (.var "a") (.var "j"))) (.var "key")))
        (s2 := (.assign (.var "i") (.binop .add (.var "i") (.intLit 1))))
        (st := insertionSortPass2AfterHiNoShiftOf base x y z)
        (st' := insertionSortPass2AfterHiWritebackOf base x y z)
        (h := insertionSort_pass2_hi_writeback_exec_of (fuel + 3) base x y z)]
  simpa using insertionSort_pass2_hi_inc_i_exec_of (fuel + 3) base x y z

theorem insertionSort_pass2_innerBody_shift_exec_of (fuel : Nat) (base : Nat) (x y z : Int)
    (hz : z < sort2Hi x y) :
    execStmt (fuel + 3) insertionInnerBody (insertionSortPass2BeforeInnerOf base x y z) =
      some (.normal (insertionSortPass2AfterHiShiftOf base x y z)) := by
  have hCond := insertionSortPass2BeforeInner_eval_branch_cond base x y z
  have hTrue : isTruthy (.int (if z < sort2Hi x y then 1 else 0)) = true := by
    simp [hz, isTruthy]
  have hIte :
      execStmt (fuel + 3) insertionInnerBody (insertionSortPass2BeforeInnerOf base x y z) =
        execStmt (fuel + 2)
          (.seq
            (.assign
              (.deref (.binop .add (.var "a") (.var "j")))
              (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1))))
            (.assign (.var "j") (.binop .sub (.var "j") (.intLit 1))))
          (insertionSortPass2BeforeInnerOf base x y z) := by
    simpa [insertionInnerBody] using
      (execStmt_ite_of_eval_true (fuel := fuel + 2)
        (cond := (.binop .lt (.var "key")
          (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1)))))
        (th := (.seq
          (.assign
            (.deref (.binop .add (.var "a") (.var "j")))
            (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1))))
          (.assign (.var "j") (.binop .sub (.var "j") (.intLit 1)))))
        (el := (.assign (.var "inserted") (.intLit 1)))
        (st := insertionSortPass2BeforeInnerOf base x y z)
        (v := .int (if z < sort2Hi x y then 1 else 0))
        hCond hTrue)
  rw [hIte]
  rw [execStmt_seq_of_normal (fuel := fuel + 1)
        (s1 := (.assign
          (.deref (.binop .add (.var "a") (.var "j")))
          (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1)))))
        (s2 := (.assign (.var "j") (.binop .sub (.var "j") (.intLit 1))))
        (st := insertionSortPass2BeforeInnerOf base x y z)
        (st' := insertionSortPass2AfterHiShiftWriteOf base x y z)
        (h := insertionSort_pass2_hi_shift_write_exec_of (fuel + 1) base x y z)]
  simpa using insertionSort_pass2_hi_shift_dec_j_exec_of fuel base x y z

private theorem insertionSortPass2AfterHiShift_lookup_a (base : Nat) (x y z : Int) :
    (insertionSortPass2AfterHiShiftOf base x y z).lookupVar "a" = some (.ptr 0 (Int.ofNat base)) := by
  calc
    (insertionSortPass2AfterHiShiftOf base x y z).lookupVar "a"
        = (insertionSortPass2AfterHiShiftWriteOf base x y z).lookupVar "a" := by
            simpa [insertionSortPass2AfterHiShiftOf] using
              (lookupVar_updateVar_ne (insertionSortPass2AfterHiShiftWriteOf base x y z) "j" "a" (.int 1)
                (by decide : "a" ≠ "j"))
    _ = (insertionSortPass2BeforeInnerOf base x y z).lookupVar "a" := by
            simp [insertionSortPass2AfterHiShiftWriteOf, CState.lookupVar]
    _ = some (.ptr 0 (Int.ofNat base)) := insertionSortPass2BeforeInner_lookup_a base x y z

private theorem insertionSortPass2AfterHiShift_lookup_j (base : Nat) (x y z : Int) :
    (insertionSortPass2AfterHiShiftOf base x y z).lookupVar "j" = some (.int 1) := by
  simpa [insertionSortPass2AfterHiShiftOf] using
    (lookupVar_updateVar_eq (insertionSortPass2AfterHiShiftWriteOf base x y z) "j" (.int 1))

private theorem insertionSortPass2AfterHiShift_lookup_key (base : Nat) (x y z : Int) :
    (insertionSortPass2AfterHiShiftOf base x y z).lookupVar "key" = some (.int z) := by
  calc
    (insertionSortPass2AfterHiShiftOf base x y z).lookupVar "key"
        = (insertionSortPass2AfterHiShiftWriteOf base x y z).lookupVar "key" := by
            simpa [insertionSortPass2AfterHiShiftOf] using
              (lookupVar_updateVar_ne (insertionSortPass2AfterHiShiftWriteOf base x y z) "j" "key" (.int 1)
                (by decide : "key" ≠ "j"))
    _ = (insertionSortPass2BeforeInnerOf base x y z).lookupVar "key" := by
            simp [insertionSortPass2AfterHiShiftWriteOf, CState.lookupVar]
    _ = some (.int z) := insertionSortPass2BeforeInner_lookup_key base x y z

private theorem insertionSortPass2AfterHiShift_lookup_i (base : Nat) (x y z : Int) :
    (insertionSortPass2AfterHiShiftOf base x y z).lookupVar "i" = some (.int 2) := by
  calc
    (insertionSortPass2AfterHiShiftOf base x y z).lookupVar "i"
        = (insertionSortPass2AfterHiShiftWriteOf base x y z).lookupVar "i" := by
            simpa [insertionSortPass2AfterHiShiftOf] using
              (lookupVar_updateVar_ne (insertionSortPass2AfterHiShiftWriteOf base x y z) "j" "i" (.int 1)
                (by decide : "i" ≠ "j"))
    _ = (insertionSortPass2BeforeInnerOf base x y z).lookupVar "i" := by
            simp [insertionSortPass2AfterHiShiftWriteOf, CState.lookupVar]
    _ = some (.int 2) := insertionSortPass2BeforeInner_lookup_i base x y z

private theorem insertionSortPass2AfterHiShift_eval_prev_lo (base : Nat) (x y z : Int) :
    evalExpr (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1)))
      (insertionSortPass2AfterHiShiftOf base x y z) = some (.int (sort2Lo x y)) := by
  have ha := insertionSortPass2AfterHiShift_lookup_a base x y z
  have hj := insertionSortPass2AfterHiShift_lookup_j base x y z
  have hSub : evalBinOp .sub (.int 1) (.int 1) = some (.int 0) := by
    native_decide
  have hAdd :
      evalBinOp .add (.ptr 0 (Int.ofNat base)) (.int 0) =
        some (CVal.ptr 0 (Int.ofNat base)) := by
    change
      (if 0 ≤ (0 : Int) then
        some (CVal.ptr 0 (Int.ofNat base + 0))
      else none) = some (CVal.ptr 0 (Int.ofNat base))
    simp
  have hReadHeap :
      (insertionSortPass2AfterHiShiftOf base x y z).heap.read base = some (.int (sort2Lo x y)) := by
    simpa [insertionSortPass2AfterHiShiftOf, insertionSortPass2AfterHiShiftWriteOf,
      insertionSortPass2BeforeInnerOf, insertionSortPass2AfterJOf, insertionSortPass2KeyOf,
      CState.updateVar] using insertionSortAfterPass1_read_base base x y z
  have hReadPtr :
      (insertionSortPass2AfterHiShiftOf base x y z).readPtr { block := 0, offset := Int.ofNat base } =
        some (.int (sort2Lo x y)) := by
    simpa [hReadHeap] using
      (CState.readPtr_block0 (insertionSortPass2AfterHiShiftOf base x y z) base base)
  simp only [evalExpr, evalStaticExpr, ha, hj, hSub, hAdd, Option.bind, Bind.bind]; exact hReadPtr

private theorem insertionSortPass2AfterHiShift_eval_branch_cond (base : Nat) (x y z : Int) :
    evalExpr
      (.binop .lt (.var "key")
        (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1))))
      (insertionSortPass2AfterHiShiftOf base x y z) =
      some (.int (if z < sort2Lo x y then 1 else 0)) := by
  simpa [evalExpr, evalStaticExpr, insertionSortPass2AfterHiShift_lookup_key base x y z,
    insertionSortPass2AfterHiShift_eval_prev_lo base x y z]

private theorem insertionSortPass2AfterHiShift_eval_loop_cond (base : Nat) (x y z : Int) :
    evalExpr insertionInnerCond (insertionSortPass2AfterHiShiftOf base x y z) = some (.int 1) := by
  have hInserted :
      (insertionSortPass2AfterHiShiftOf base x y z).lookupVar "inserted" = some (.int 0) := by
    calc
      (insertionSortPass2AfterHiShiftOf base x y z).lookupVar "inserted"
          = (insertionSortPass2AfterHiShiftWriteOf base x y z).lookupVar "inserted" := by
              simpa [insertionSortPass2AfterHiShiftOf] using
                (lookupVar_updateVar_ne (insertionSortPass2AfterHiShiftWriteOf base x y z) "j" "inserted" (.int 1)
                  (by decide : "inserted" ≠ "j"))
      _ = (insertionSortPass2BeforeInnerOf base x y z).lookupVar "inserted" := by
            simp [insertionSortPass2AfterHiShiftWriteOf, CState.lookupVar]
      _ = some (.int 0) := by
            simpa [insertionSortPass2BeforeInnerOf] using
              (lookupVar_updateVar_eq (insertionSortPass2AfterJOf base x y z) "inserted" (.int 0))
  simp [insertionInnerCond, evalExpr, evalStaticExpr,
    insertionSortPass2AfterHiShift_lookup_j base x y z, hInserted, isTruthy]

theorem insertionSort_pass2_mid_set_inserted_exec_of (fuel : Nat) (base : Nat) (x y z : Int) :
    execStmt (fuel + 1) (.assign (.var "inserted") (.intLit 1))
      (insertionSortPass2AfterHiShiftOf base x y z) =
      some (.normal (insertionSortPass2AfterMidNoShiftOf base x y z)) := by
  simp [execStmt, insertionSortPass2AfterMidNoShiftOf, insertionSortPass2AfterHiShiftOf,
    insertionSortPass2AfterHiShiftWriteOf, insertionSortPass2BeforeInnerOf,
    insertionSortPass2AfterJOf, insertionSortPass2KeyOf, evalExpr, evalStaticExpr, CState.updateVar]

theorem insertionSort_pass2_lo_shift_write_exec_of (fuel : Nat) (base : Nat) (x y z : Int) :
    execStmt (fuel + 1)
      (.assign
        (.deref (.binop .add (.var "a") (.var "j")))
        (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1))))
      (insertionSortPass2AfterHiShiftOf base x y z) =
      some (.normal (insertionSortPass2AfterLoShiftWriteOf base x y z)) := by
  have hRhs := insertionSortPass2AfterHiShift_eval_prev_lo base x y z
  have ha := insertionSortPass2AfterHiShift_lookup_a base x y z
  have hj := insertionSortPass2AfterHiShift_lookup_j base x y z
  have hPtr :
      evalExpr (.binop .add (.var "a") (.var "j")) (insertionSortPass2AfterHiShiftOf base x y z) =
        some (CVal.ptr 0 (Int.ofNat (base + 1))) := by
    have hAdd :
        evalBinOp .add (.ptr 0 (Int.ofNat base)) (.int 1) =
          some (CVal.ptr 0 (Int.ofNat (base + 1))) := by
      change
        (if 0 ≤ (1 : Int) then
          some (CVal.ptr 0 (Int.ofNat base + 1))
        else none) = some (CVal.ptr 0 (Int.ofNat (base + 1)))
      simp
    simp only [evalExpr, evalStaticExpr, ha, hj, hAdd, Option.bind, Bind.bind]
  let st1 := insertionSortPass2AfterHiShiftOf base x y z
  let st2 := insertionSortPass2AfterLoShiftWriteOf base x y z
  have hWrite :
      st1.writePtr { block := 0, offset := Int.ofNat (base + 1) } (.int (sort2Lo x y)) = some st2 := by
    simpa [st1, st2, insertionSortPass2AfterLoShiftWriteOf] using
      (CState.writePtr_block0 st1 (base + 1) (base + 1) (.int (sort2Lo x y)))
  simpa [execStmt, hRhs, hPtr] using congrArg (Option.map ExecResult.normal) hWrite

theorem insertionSort_pass2_lo_shift_dec_j_exec_of (fuel : Nat) (base : Nat) (x y z : Int) :
    execStmt (fuel + 1) (.assign (.var "j") (.binop .sub (.var "j") (.intLit 1)))
      (insertionSortPass2AfterLoShiftWriteOf base x y z) =
      some (.normal (insertionSortPass2AfterLoShiftOf base x y z)) := by
  have hj :
      (insertionSortPass2AfterLoShiftWriteOf base x y z).lookupVar "j" = some (.int 1) := by
    calc
      (insertionSortPass2AfterLoShiftWriteOf base x y z).lookupVar "j"
          = (insertionSortPass2AfterHiShiftOf base x y z).lookupVar "j" := by
              simp [insertionSortPass2AfterLoShiftWriteOf, CState.lookupVar]
      _ = some (.int 1) := insertionSortPass2AfterHiShift_lookup_j base x y z
  have hSub : evalBinOp .sub (.int 1) (.int 1) = some (.int 0) := by
    native_decide
  change
    (((insertionSortPass2AfterLoShiftWriteOf base x y z).lookupVar "j").bind
      (fun v1 => evalBinOp .sub v1 (.int 1))).bind
      (fun v =>
        some (ExecResult.normal ((insertionSortPass2AfterLoShiftWriteOf base x y z).updateVar "j" v))) =
      some (ExecResult.normal (insertionSortPass2AfterLoShiftOf base x y z))
  rw [hj]
  simpa [hSub, insertionSortPass2AfterLoShiftOf]

theorem insertionSort_pass2_innerBody_mid_exec_of (fuel : Nat) (base : Nat) (x y z : Int)
    (hzHi : z < sort2Hi x y) (hzLo : ¬ z < sort2Lo x y) :
    execStmt (fuel + 3) insertionInnerBody (insertionSortPass2AfterHiShiftOf base x y z) =
      some (.normal (insertionSortPass2AfterMidNoShiftOf base x y z)) := by
  have hCond := insertionSortPass2AfterHiShift_eval_branch_cond base x y z
  have hFalse : isTruthy (.int (if z < sort2Lo x y then 1 else 0)) = false := by
    simp [hzLo, isTruthy]
  have hIte :
      execStmt (fuel + 3) insertionInnerBody (insertionSortPass2AfterHiShiftOf base x y z) =
        execStmt (fuel + 2) (.assign (.var "inserted") (.intLit 1))
          (insertionSortPass2AfterHiShiftOf base x y z) := by
    simpa [insertionInnerBody] using
      (execStmt_ite_of_eval_false (fuel := fuel + 2)
        (cond := (.binop .lt (.var "key")
          (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1)))))
        (th := (.seq
          (.assign
            (.deref (.binop .add (.var "a") (.var "j")))
            (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1))))
          (.assign (.var "j") (.binop .sub (.var "j") (.intLit 1)))))
        (el := (.assign (.var "inserted") (.intLit 1)))
        (st := insertionSortPass2AfterHiShiftOf base x y z)
        (v := .int (if z < sort2Lo x y then 1 else 0))
        hCond hFalse)
  rw [hIte]
  simpa using insertionSort_pass2_mid_set_inserted_exec_of (fuel + 1) base x y z

theorem insertionSort_pass2_innerBody_low_exec_of (fuel : Nat) (base : Nat) (x y z : Int)
    (hzLo : z < sort2Lo x y) :
    execStmt (fuel + 3) insertionInnerBody (insertionSortPass2AfterHiShiftOf base x y z) =
      some (.normal (insertionSortPass2AfterLoShiftOf base x y z)) := by
  have hCond := insertionSortPass2AfterHiShift_eval_branch_cond base x y z
  have hTrue : isTruthy (.int (if z < sort2Lo x y then 1 else 0)) = true := by
    simp [hzLo, isTruthy]
  have hIte :
      execStmt (fuel + 3) insertionInnerBody (insertionSortPass2AfterHiShiftOf base x y z) =
        execStmt (fuel + 2)
          (.seq
            (.assign
              (.deref (.binop .add (.var "a") (.var "j")))
              (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1))))
            (.assign (.var "j") (.binop .sub (.var "j") (.intLit 1))))
          (insertionSortPass2AfterHiShiftOf base x y z) := by
    simpa [insertionInnerBody] using
      (execStmt_ite_of_eval_true (fuel := fuel + 2)
        (cond := (.binop .lt (.var "key")
          (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1)))))
        (th := (.seq
          (.assign
            (.deref (.binop .add (.var "a") (.var "j")))
            (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1))))
          (.assign (.var "j") (.binop .sub (.var "j") (.intLit 1)))))
        (el := (.assign (.var "inserted") (.intLit 1)))
        (st := insertionSortPass2AfterHiShiftOf base x y z)
        (v := .int (if z < sort2Lo x y then 1 else 0))
        hCond hTrue)
  rw [hIte]
  rw [execStmt_seq_of_normal (fuel := fuel + 1)
        (s1 := (.assign
          (.deref (.binop .add (.var "a") (.var "j")))
          (.arrayAccess (.var "a") (.binop .sub (.var "j") (.intLit 1)))))
        (s2 := (.assign (.var "j") (.binop .sub (.var "j") (.intLit 1))))
        (st := insertionSortPass2AfterHiShiftOf base x y z)
        (st' := insertionSortPass2AfterLoShiftWriteOf base x y z)
        (h := insertionSort_pass2_lo_shift_write_exec_of (fuel + 1) base x y z)]
  simpa using insertionSort_pass2_lo_shift_dec_j_exec_of fuel base x y z

private theorem insertionSortPass2AfterMidNoShift_lookup_a (base : Nat) (x y z : Int) :
    (insertionSortPass2AfterMidNoShiftOf base x y z).lookupVar "a" = some (.ptr 0 (Int.ofNat base)) := by
  calc
    (insertionSortPass2AfterMidNoShiftOf base x y z).lookupVar "a"
        = (insertionSortPass2AfterHiShiftOf base x y z).lookupVar "a" := by
            simpa [insertionSortPass2AfterMidNoShiftOf] using
              (lookupVar_updateVar_ne (insertionSortPass2AfterHiShiftOf base x y z) "inserted" "a" (.int 1)
                (by decide : "a" ≠ "inserted"))
    _ = some (.ptr 0 (Int.ofNat base)) := insertionSortPass2AfterHiShift_lookup_a base x y z

private theorem insertionSortPass2AfterMidNoShift_lookup_j (base : Nat) (x y z : Int) :
    (insertionSortPass2AfterMidNoShiftOf base x y z).lookupVar "j" = some (.int 1) := by
  calc
    (insertionSortPass2AfterMidNoShiftOf base x y z).lookupVar "j"
        = (insertionSortPass2AfterHiShiftOf base x y z).lookupVar "j" := by
            simpa [insertionSortPass2AfterMidNoShiftOf] using
              (lookupVar_updateVar_ne (insertionSortPass2AfterHiShiftOf base x y z) "inserted" "j" (.int 1)
                (by decide : "j" ≠ "inserted"))
    _ = some (.int 1) := insertionSortPass2AfterHiShift_lookup_j base x y z

private theorem insertionSortPass2AfterMidNoShift_lookup_key (base : Nat) (x y z : Int) :
    (insertionSortPass2AfterMidNoShiftOf base x y z).lookupVar "key" = some (.int z) := by
  calc
    (insertionSortPass2AfterMidNoShiftOf base x y z).lookupVar "key"
        = (insertionSortPass2AfterHiShiftOf base x y z).lookupVar "key" := by
            simpa [insertionSortPass2AfterMidNoShiftOf] using
              (lookupVar_updateVar_ne (insertionSortPass2AfterHiShiftOf base x y z) "inserted" "key" (.int 1)
                (by decide : "key" ≠ "inserted"))
    _ = some (.int z) := insertionSortPass2AfterHiShift_lookup_key base x y z

private theorem insertionSortPass2AfterMidNoShift_lookup_i (base : Nat) (x y z : Int) :
    (insertionSortPass2AfterMidNoShiftOf base x y z).lookupVar "i" = some (.int 2) := by
  calc
    (insertionSortPass2AfterMidNoShiftOf base x y z).lookupVar "i"
        = (insertionSortPass2AfterHiShiftOf base x y z).lookupVar "i" := by
            simpa [insertionSortPass2AfterMidNoShiftOf] using
              (lookupVar_updateVar_ne (insertionSortPass2AfterHiShiftOf base x y z) "inserted" "i" (.int 1)
                (by decide : "i" ≠ "inserted"))
    _ = some (.int 2) := insertionSortPass2AfterHiShift_lookup_i base x y z

private theorem insertionSortPass2AfterMidNoShift_eval_writeback_target (base : Nat) (x y z : Int) :
    evalExpr (.binop .add (.var "a") (.var "j")) (insertionSortPass2AfterMidNoShiftOf base x y z) =
      some (CVal.ptr 0 (Int.ofNat (base + 1))) := by
  have ha := insertionSortPass2AfterMidNoShift_lookup_a base x y z
  have hj := insertionSortPass2AfterMidNoShift_lookup_j base x y z
  have hAdd :
      evalBinOp .add (.ptr 0 (Int.ofNat base)) (.int 1) =
        some (CVal.ptr 0 (Int.ofNat (base + 1))) := by
    change
      (if 0 ≤ (1 : Int) then
        some (CVal.ptr 0 (Int.ofNat base + 1))
      else none) = some (CVal.ptr 0 (Int.ofNat (base + 1)))
    simp
  simp only [evalExpr, evalStaticExpr, ha, hj, hAdd, Option.bind, Bind.bind]

private theorem insertionSortPass2AfterMidNoShift_eval_loop_cond (base : Nat) (x y z : Int) :
    evalExpr insertionInnerCond (insertionSortPass2AfterMidNoShiftOf base x y z) = some (.int 0) := by
  have hInserted :
      (insertionSortPass2AfterMidNoShiftOf base x y z).lookupVar "inserted" = some (.int 1) := by
    simpa [insertionSortPass2AfterMidNoShiftOf] using
      (lookupVar_updateVar_eq (insertionSortPass2AfterHiShiftOf base x y z) "inserted" (.int 1))
  simp [insertionInnerCond, evalExpr, evalStaticExpr,
    insertionSortPass2AfterMidNoShift_lookup_j base x y z, hInserted, isTruthy]

private theorem insertionSortPass2AfterLoShift_lookup_a (base : Nat) (x y z : Int) :
    (insertionSortPass2AfterLoShiftOf base x y z).lookupVar "a" = some (.ptr 0 (Int.ofNat base)) := by
  calc
    (insertionSortPass2AfterLoShiftOf base x y z).lookupVar "a"
        = (insertionSortPass2AfterLoShiftWriteOf base x y z).lookupVar "a" := by
            simpa [insertionSortPass2AfterLoShiftOf] using
              (lookupVar_updateVar_ne (insertionSortPass2AfterLoShiftWriteOf base x y z) "j" "a" (.int 0)
                (by decide : "a" ≠ "j"))
    _ = (insertionSortPass2AfterHiShiftOf base x y z).lookupVar "a" := by
            simp [insertionSortPass2AfterLoShiftWriteOf, CState.lookupVar]
    _ = some (.ptr 0 (Int.ofNat base)) := insertionSortPass2AfterHiShift_lookup_a base x y z

private theorem insertionSortPass2AfterLoShift_lookup_j (base : Nat) (x y z : Int) :
    (insertionSortPass2AfterLoShiftOf base x y z).lookupVar "j" = some (.int 0) := by
  simpa [insertionSortPass2AfterLoShiftOf] using
    (lookupVar_updateVar_eq (insertionSortPass2AfterLoShiftWriteOf base x y z) "j" (.int 0))

private theorem insertionSortPass2AfterLoShift_lookup_key (base : Nat) (x y z : Int) :
    (insertionSortPass2AfterLoShiftOf base x y z).lookupVar "key" = some (.int z) := by
  calc
    (insertionSortPass2AfterLoShiftOf base x y z).lookupVar "key"
        = (insertionSortPass2AfterLoShiftWriteOf base x y z).lookupVar "key" := by
            simpa [insertionSortPass2AfterLoShiftOf] using
              (lookupVar_updateVar_ne (insertionSortPass2AfterLoShiftWriteOf base x y z) "j" "key" (.int 0)
                (by decide : "key" ≠ "j"))
    _ = (insertionSortPass2AfterHiShiftOf base x y z).lookupVar "key" := by
            simp [insertionSortPass2AfterLoShiftWriteOf, CState.lookupVar]
    _ = some (.int z) := insertionSortPass2AfterHiShift_lookup_key base x y z

private theorem insertionSortPass2AfterLoShift_lookup_i (base : Nat) (x y z : Int) :
    (insertionSortPass2AfterLoShiftOf base x y z).lookupVar "i" = some (.int 2) := by
  calc
    (insertionSortPass2AfterLoShiftOf base x y z).lookupVar "i"
        = (insertionSortPass2AfterLoShiftWriteOf base x y z).lookupVar "i" := by
            simpa [insertionSortPass2AfterLoShiftOf] using
              (lookupVar_updateVar_ne (insertionSortPass2AfterLoShiftWriteOf base x y z) "j" "i" (.int 0)
                (by decide : "i" ≠ "j"))
    _ = (insertionSortPass2AfterHiShiftOf base x y z).lookupVar "i" := by
            simp [insertionSortPass2AfterLoShiftWriteOf, CState.lookupVar]
    _ = some (.int 2) := insertionSortPass2AfterHiShift_lookup_i base x y z

private theorem insertionSortPass2AfterLoShift_eval_writeback_target (base : Nat) (x y z : Int) :
    evalExpr (.binop .add (.var "a") (.var "j")) (insertionSortPass2AfterLoShiftOf base x y z) =
      some (CVal.ptr 0 (Int.ofNat base)) := by
  have ha := insertionSortPass2AfterLoShift_lookup_a base x y z
  have hj := insertionSortPass2AfterLoShift_lookup_j base x y z
  have hAdd :
      evalBinOp .add (.ptr 0 (Int.ofNat base)) (.int 0) =
        some (CVal.ptr 0 (Int.ofNat base)) := by
    change
      (if 0 ≤ (0 : Int) then
        some (CVal.ptr 0 (Int.ofNat base + 0))
      else none) = some (CVal.ptr 0 (Int.ofNat base))
    simp
  simp only [evalExpr, evalStaticExpr, ha, hj, hAdd, Option.bind, Bind.bind]

private theorem insertionSortPass2AfterLoShift_eval_loop_cond (base : Nat) (x y z : Int) :
    evalExpr insertionInnerCond (insertionSortPass2AfterLoShiftOf base x y z) = some (.int 0) := by
  have hInserted :
      (insertionSortPass2AfterLoShiftOf base x y z).lookupVar "inserted" = some (.int 0) := by
    calc
      (insertionSortPass2AfterLoShiftOf base x y z).lookupVar "inserted"
          = (insertionSortPass2AfterLoShiftWriteOf base x y z).lookupVar "inserted" := by
              simpa [insertionSortPass2AfterLoShiftOf] using
                (lookupVar_updateVar_ne (insertionSortPass2AfterLoShiftWriteOf base x y z) "j" "inserted" (.int 0)
                  (by decide : "inserted" ≠ "j"))
      _ = (insertionSortPass2AfterHiShiftOf base x y z).lookupVar "inserted" := by
            simp [insertionSortPass2AfterLoShiftWriteOf, CState.lookupVar]
      _ = some (.int 0) := by
            calc
              (insertionSortPass2AfterHiShiftOf base x y z).lookupVar "inserted"
                  = (insertionSortPass2AfterHiShiftWriteOf base x y z).lookupVar "inserted" := by
                      simpa [insertionSortPass2AfterHiShiftOf] using
                        (lookupVar_updateVar_ne (insertionSortPass2AfterHiShiftWriteOf base x y z) "j" "inserted" (.int 1)
                          (by decide : "inserted" ≠ "j"))
              _ = (insertionSortPass2BeforeInnerOf base x y z).lookupVar "inserted" := by
                    simp [insertionSortPass2AfterHiShiftWriteOf, CState.lookupVar]
              _ = some (.int 0) := by
                    simpa [insertionSortPass2BeforeInnerOf] using
                      (lookupVar_updateVar_eq (insertionSortPass2AfterJOf base x y z) "inserted" (.int 0))
  simp [insertionInnerCond, evalExpr, evalStaticExpr,
    insertionSortPass2AfterLoShift_lookup_j base x y z, hInserted, isTruthy]

theorem insertionSort_pass2_mid_writeback_exec_of (fuel : Nat) (base : Nat) (x y z : Int) :
    execStmt (fuel + 1) (.assign (.deref (.binop .add (.var "a") (.var "j"))) (.var "key"))
      (insertionSortPass2AfterMidNoShiftOf base x y z) =
      some (.normal (insertionSortPass2AfterMidWritebackOf base x y z)) := by
  have hKey := insertionSortPass2AfterMidNoShift_lookup_key base x y z
  have hPtr := insertionSortPass2AfterMidNoShift_eval_writeback_target base x y z
  let st1 := insertionSortPass2AfterMidNoShiftOf base x y z
  let st2 := insertionSortPass2AfterMidWritebackOf base x y z
  have hWrite :
      st1.writePtr { block := 0, offset := Int.ofNat (base + 1) } (.int z) = some st2 := by
    simpa [st1, st2, insertionSortPass2AfterMidWritebackOf] using
      (CState.writePtr_block0 st1 (base + 1) (base + 1) (.int z))
  simpa [execStmt, hPtr] using
    (show (evalExpr (.var "key") (insertionSortPass2AfterMidNoShiftOf base x y z)).bind
        (fun v =>
          ExecResult.normal <$> (insertionSortPass2AfterMidNoShiftOf base x y z).writePtr
            { block := 0, offset := Int.ofNat (base + 1) } v) =
      some (.normal (insertionSortPass2AfterMidWritebackOf base x y z)) from by
        rw [show evalExpr (.var "key") (insertionSortPass2AfterMidNoShiftOf base x y z) = some (.int z) by
              simp only [evalExpr, Option.bind, Bind.bind]; exact hKey]
        simpa using congrArg (Option.map ExecResult.normal) hWrite)

theorem insertionSort_pass2_lo_writeback_exec_of (fuel : Nat) (base : Nat) (x y z : Int) :
    execStmt (fuel + 1) (.assign (.deref (.binop .add (.var "a") (.var "j"))) (.var "key"))
      (insertionSortPass2AfterLoShiftOf base x y z) =
      some (.normal (insertionSortPass2AfterLoWritebackOf base x y z)) := by
  have hKey := insertionSortPass2AfterLoShift_lookup_key base x y z
  have hPtr := insertionSortPass2AfterLoShift_eval_writeback_target base x y z
  let st1 := insertionSortPass2AfterLoShiftOf base x y z
  let st2 := insertionSortPass2AfterLoWritebackOf base x y z
  have hWrite :
      st1.writePtr { block := 0, offset := Int.ofNat base } (.int z) = some st2 := by
    simpa [st1, st2, insertionSortPass2AfterLoWritebackOf] using
      (CState.writePtr_block0 st1 base base (.int z))
  simpa [execStmt, hPtr] using
    (show (evalExpr (.var "key") (insertionSortPass2AfterLoShiftOf base x y z)).bind
        (fun v =>
          ExecResult.normal <$> (insertionSortPass2AfterLoShiftOf base x y z).writePtr
            { block := 0, offset := Int.ofNat base } v) =
      some (.normal (insertionSortPass2AfterLoWritebackOf base x y z)) from by
        rw [show evalExpr (.var "key") (insertionSortPass2AfterLoShiftOf base x y z) = some (.int z) by
              simp only [evalExpr, Option.bind, Bind.bind]; exact hKey]
        simpa using congrArg (Option.map ExecResult.normal) hWrite)

theorem insertionSort_pass2_mid_inc_i_exec_of (fuel : Nat) (base : Nat) (x y z : Int) :
    execStmt (fuel + 1) (.assign (.var "i") (.binop .add (.var "i") (.intLit 1)))
      (insertionSortPass2AfterMidWritebackOf base x y z) =
      some (.normal (insertionSortPass2AfterMidOf base x y z)) := by
  have hi : (insertionSortPass2AfterMidWritebackOf base x y z).lookupVar "i" = some (.int 2) := by
    calc
      (insertionSortPass2AfterMidWritebackOf base x y z).lookupVar "i"
          = (insertionSortPass2AfterMidNoShiftOf base x y z).lookupVar "i" := by
              simp [insertionSortPass2AfterMidWritebackOf, CState.lookupVar]
      _ = some (.int 2) := insertionSortPass2AfterMidNoShift_lookup_i base x y z
  have hAdd : evalBinOp .add (.int 2) (.int 1) = some (.int 3) := by
    native_decide
  change
    (((insertionSortPass2AfterMidWritebackOf base x y z).lookupVar "i").bind
      (fun v1 => evalBinOp .add v1 (.int 1))).bind
      (fun v =>
        some (ExecResult.normal ((insertionSortPass2AfterMidWritebackOf base x y z).updateVar "i" v))) =
      some (.normal (insertionSortPass2AfterMidOf base x y z))
  rw [hi]
  simpa [hAdd, insertionSortPass2AfterMidOf]

theorem insertionSort_pass2_lo_inc_i_exec_of (fuel : Nat) (base : Nat) (x y z : Int) :
    execStmt (fuel + 1) (.assign (.var "i") (.binop .add (.var "i") (.intLit 1)))
      (insertionSortPass2AfterLoWritebackOf base x y z) =
      some (.normal (insertionSortPass2AfterLoOf base x y z)) := by
  have hi : (insertionSortPass2AfterLoWritebackOf base x y z).lookupVar "i" = some (.int 2) := by
    calc
      (insertionSortPass2AfterLoWritebackOf base x y z).lookupVar "i"
          = (insertionSortPass2AfterLoShiftOf base x y z).lookupVar "i" := by
              simp [insertionSortPass2AfterLoWritebackOf, CState.lookupVar]
      _ = some (.int 2) := insertionSortPass2AfterLoShift_lookup_i base x y z
  have hAdd : evalBinOp .add (.int 2) (.int 1) = some (.int 3) := by
    native_decide
  change
    (((insertionSortPass2AfterLoWritebackOf base x y z).lookupVar "i").bind
      (fun v1 => evalBinOp .add v1 (.int 1))).bind
      (fun v =>
        some (ExecResult.normal ((insertionSortPass2AfterLoWritebackOf base x y z).updateVar "i" v))) =
      some (.normal (insertionSortPass2AfterLoOf base x y z))
  rw [hi]
  simpa [hAdd, insertionSortPass2AfterLoOf]

theorem insertionSort_pass2_innerWhile_mid_exec_of (fuel : Nat) (base : Nat) (x y z : Int)
    (hzHi : z < sort2Hi x y) (hzLo : ¬ z < sort2Lo x y) :
    execStmt (fuel + 7) (.whileInv insertionInnerCond HProp.htrue insertionInnerBody)
      (insertionSortPass2BeforeInnerOf base x y z) =
      some (.normal (insertionSortPass2AfterMidNoShiftOf base x y z)) := by
  rw [execStmt_whileInv_of_eval_true_normal (fuel := fuel + 6)
        (cond := insertionInnerCond) (inv := HProp.htrue) (body := insertionInnerBody)
        (st := insertionSortPass2BeforeInnerOf base x y z)
        (st' := insertionSortPass2AfterHiShiftOf base x y z)
        (v := .int 1)
        (hEval := insertionSortPass2BeforeInner_eval_loop_cond base x y z)
        (hTruth := by simp [isTruthy])
        (hBody := insertionSort_pass2_innerBody_shift_exec_of (fuel + 3) base x y z hzHi)]
  rw [execStmt_whileInv_of_eval_true_normal (fuel := fuel + 5)
        (cond := insertionInnerCond) (inv := HProp.htrue) (body := insertionInnerBody)
        (st := insertionSortPass2AfterHiShiftOf base x y z)
        (st' := insertionSortPass2AfterMidNoShiftOf base x y z)
        (v := .int 1)
        (hEval := insertionSortPass2AfterHiShift_eval_loop_cond base x y z)
        (hTruth := by simp [isTruthy])
        (hBody := insertionSort_pass2_innerBody_mid_exec_of (fuel + 2) base x y z hzHi hzLo)]
  exact execStmt_whileInv_of_eval_false (fuel := fuel + 4) (cond := insertionInnerCond)
    (inv := HProp.htrue) (body := insertionInnerBody) (st := insertionSortPass2AfterMidNoShiftOf base x y z)
    (v := .int 0) (hEval := insertionSortPass2AfterMidNoShift_eval_loop_cond base x y z)
    (hTruth := by simp [isTruthy])

theorem insertionSort_pass2_innerWhile_low_exec_of (fuel : Nat) (base : Nat) (x y z : Int)
    (hzHi : z < sort2Hi x y) (hzLo : z < sort2Lo x y) :
    execStmt (fuel + 7) (.whileInv insertionInnerCond HProp.htrue insertionInnerBody)
      (insertionSortPass2BeforeInnerOf base x y z) =
      some (.normal (insertionSortPass2AfterLoShiftOf base x y z)) := by
  rw [execStmt_whileInv_of_eval_true_normal (fuel := fuel + 6)
        (cond := insertionInnerCond) (inv := HProp.htrue) (body := insertionInnerBody)
        (st := insertionSortPass2BeforeInnerOf base x y z)
        (st' := insertionSortPass2AfterHiShiftOf base x y z)
        (v := .int 1)
        (hEval := insertionSortPass2BeforeInner_eval_loop_cond base x y z)
        (hTruth := by simp [isTruthy])
        (hBody := insertionSort_pass2_innerBody_shift_exec_of (fuel + 3) base x y z hzHi)]
  rw [execStmt_whileInv_of_eval_true_normal (fuel := fuel + 5)
        (cond := insertionInnerCond) (inv := HProp.htrue) (body := insertionInnerBody)
        (st := insertionSortPass2AfterHiShiftOf base x y z)
        (st' := insertionSortPass2AfterLoShiftOf base x y z)
        (v := .int 1)
        (hEval := insertionSortPass2AfterHiShift_eval_loop_cond base x y z)
        (hTruth := by simp [isTruthy])
        (hBody := insertionSort_pass2_innerBody_low_exec_of (fuel + 2) base x y z hzLo)]
  exact execStmt_whileInv_of_eval_false (fuel := fuel + 4) (cond := insertionInnerCond)
    (inv := HProp.htrue) (body := insertionInnerBody) (st := insertionSortPass2AfterLoShiftOf base x y z)
    (v := .int 0) (hEval := insertionSortPass2AfterLoShift_eval_loop_cond base x y z)
    (hTruth := by simp [isTruthy])

theorem insertionSort_pass2_mid_exec_of (fuel : Nat) (base : Nat) (x y z : Int)
    (hzHi : z < sort2Hi x y) (hzLo : ¬ z < sort2Lo x y) :
    execStmt (fuel + 9) insertionSortSuffixBody (insertionSortPass2BeforeInnerOf base x y z) =
      some (.normal (insertionSortPass2AfterMidOf base x y z)) := by
  have hSeq :
      execStmt (fuel + 9) insertionSortSuffixBody (insertionSortPass2BeforeInnerOf base x y z) =
        execStmt (fuel + 8)
          (.seq
            (.assign (.deref (.binop .add (.var "a") (.var "j"))) (.var "key"))
            (.assign (.var "i") (.binop .add (.var "i") (.intLit 1))))
          (insertionSortPass2AfterMidNoShiftOf base x y z) := by
    simpa [insertionSortSuffixBody] using
      (execStmt_seq_of_normal (fuel := fuel + 8)
        (s1 := (.whileInv insertionInnerCond HProp.htrue insertionInnerBody))
        (s2 := (.seq
          (.assign (.deref (.binop .add (.var "a") (.var "j"))) (.var "key"))
          (.assign (.var "i") (.binop .add (.var "i") (.intLit 1)))))
        (st := insertionSortPass2BeforeInnerOf base x y z)
        (st' := insertionSortPass2AfterMidNoShiftOf base x y z)
        (h := insertionSort_pass2_innerWhile_mid_exec_of (fuel + 1) base x y z hzHi hzLo))
  rw [hSeq]
  rw [execStmt_seq_of_normal (fuel := fuel + 7)
        (s1 := (.assign (.deref (.binop .add (.var "a") (.var "j"))) (.var "key")))
        (s2 := (.assign (.var "i") (.binop .add (.var "i") (.intLit 1))))
        (st := insertionSortPass2AfterMidNoShiftOf base x y z)
        (st' := insertionSortPass2AfterMidWritebackOf base x y z)
        (h := insertionSort_pass2_mid_writeback_exec_of (fuel + 6) base x y z)]
  simpa using insertionSort_pass2_mid_inc_i_exec_of (fuel + 6) base x y z

theorem insertionSort_pass2_low_exec_of (fuel : Nat) (base : Nat) (x y z : Int)
    (hzHi : z < sort2Hi x y) (hzLo : z < sort2Lo x y) :
    execStmt (fuel + 9) insertionSortSuffixBody (insertionSortPass2BeforeInnerOf base x y z) =
      some (.normal (insertionSortPass2AfterLoOf base x y z)) := by
  have hSeq :
      execStmt (fuel + 9) insertionSortSuffixBody (insertionSortPass2BeforeInnerOf base x y z) =
        execStmt (fuel + 8)
          (.seq
            (.assign (.deref (.binop .add (.var "a") (.var "j"))) (.var "key"))
            (.assign (.var "i") (.binop .add (.var "i") (.intLit 1))))
          (insertionSortPass2AfterLoShiftOf base x y z) := by
    simpa [insertionSortSuffixBody] using
      (execStmt_seq_of_normal (fuel := fuel + 8)
        (s1 := (.whileInv insertionInnerCond HProp.htrue insertionInnerBody))
        (s2 := (.seq
          (.assign (.deref (.binop .add (.var "a") (.var "j"))) (.var "key"))
          (.assign (.var "i") (.binop .add (.var "i") (.intLit 1)))))
        (st := insertionSortPass2BeforeInnerOf base x y z)
        (st' := insertionSortPass2AfterLoShiftOf base x y z)
        (h := insertionSort_pass2_innerWhile_low_exec_of (fuel + 1) base x y z hzHi hzLo))
  rw [hSeq]
  rw [execStmt_seq_of_normal (fuel := fuel + 7)
        (s1 := (.assign (.deref (.binop .add (.var "a") (.var "j"))) (.var "key")))
        (s2 := (.assign (.var "i") (.binop .add (.var "i") (.intLit 1))))
        (st := insertionSortPass2AfterLoShiftOf base x y z)
        (st' := insertionSortPass2AfterLoWritebackOf base x y z)
        (h := insertionSort_pass2_lo_writeback_exec_of (fuel + 6) base x y z)]
  simpa using insertionSort_pass2_lo_inc_i_exec_of (fuel + 6) base x y z

private theorem insertionSortAfterInit_eval_outer_cond (base : Nat) (x y z : Int) :
    evalExpr (.binop .lt (.var "i") (.var "n")) (insertionSortAfterInitOf base x y z) =
      some (.int 1) := by
  simp [evalExpr, evalStaticExpr, insertionSortAfterInitOf, CState.lookupVar, List.lookup]

private theorem insertionSortAfterPass1_lookup_n (base : Nat) (x y z : Int) :
    (insertionSortAfterPass1Of base x y z).lookupVar "n" = some (.int 3) := by
  by_cases hxy : y < x
  · simp [insertionSortAfterPass1Of, hxy, insertionSortAfterShiftWritebackOf,
      insertionSortAfterShiftOf, insertionSortAfterShiftWriteOf, insertionSortBeforeInnerOf,
      insertionSortAfterJOf, insertionSortAfterKeyOf, insertionSortAfterInitOf, CState.lookupVar,
      CState.updateVar, List.lookup]
  · simp [insertionSortAfterPass1Of, hxy, insertionSortAfterNoShiftWritebackOf,
      insertionSortAfterNoShiftOf, insertionSortBeforeInnerOf, insertionSortAfterJOf,
      insertionSortAfterKeyOf, insertionSortAfterInitOf, CState.lookupVar, CState.updateVar,
      List.lookup]

private theorem insertionSortAfterPass1_eval_outer_cond (base : Nat) (x y z : Int) :
    evalExpr (.binop .lt (.var "i") (.var "n")) (insertionSortAfterPass1Of base x y z) =
      some (.int 1) := by
  simp [evalExpr, evalStaticExpr, insertionSortAfterPass1_lookup_i base x y z,
    insertionSortAfterPass1_lookup_n base x y z]

private theorem insertionSortPass2AfterHi_lookup_a (base : Nat) (x y z : Int) :
    (insertionSortPass2AfterHiOf base x y z).lookupVar "a" = some (.ptr 0 (Int.ofNat base)) := by
  calc
    (insertionSortPass2AfterHiOf base x y z).lookupVar "a"
        = (insertionSortPass2AfterHiWritebackOf base x y z).lookupVar "a" := by
            simpa [insertionSortPass2AfterHiOf] using
              (lookupVar_updateVar_ne (insertionSortPass2AfterHiWritebackOf base x y z) "i" "a" (.int 3)
                (by decide : "a" ≠ "i"))
    _ = (insertionSortPass2AfterHiNoShiftOf base x y z).lookupVar "a" := by
          simp [insertionSortPass2AfterHiWritebackOf, CState.lookupVar]
    _ = some (.ptr 0 (Int.ofNat base)) := insertionSortPass2AfterHiNoShift_lookup_a base x y z

private theorem insertionSortPass2AfterHi_lookup_n (base : Nat) (x y z : Int) :
    (insertionSortPass2AfterHiOf base x y z).lookupVar "n" = some (.int 3) := by
  calc
    (insertionSortPass2AfterHiOf base x y z).lookupVar "n"
        = (insertionSortPass2AfterHiWritebackOf base x y z).lookupVar "n" := by
            simpa [insertionSortPass2AfterHiOf] using
              (lookupVar_updateVar_ne (insertionSortPass2AfterHiWritebackOf base x y z) "i" "n" (.int 3)
                (by decide : "n" ≠ "i"))
    _ = (insertionSortPass2AfterHiNoShiftOf base x y z).lookupVar "n" := by
          simp [insertionSortPass2AfterHiWritebackOf, CState.lookupVar]
    _ = (insertionSortPass2BeforeInnerOf base x y z).lookupVar "n" := by
          simpa [insertionSortPass2AfterHiNoShiftOf] using
            (lookupVar_updateVar_ne (insertionSortPass2BeforeInnerOf base x y z) "inserted" "n" (.int 1)
              (by decide : "n" ≠ "inserted"))
    _ = (insertionSortPass2AfterJOf base x y z).lookupVar "n" := by
          simpa [insertionSortPass2BeforeInnerOf] using
            (lookupVar_updateVar_ne (insertionSortPass2AfterJOf base x y z) "inserted" "n" (.int 0)
              (by decide : "n" ≠ "inserted"))
    _ = (insertionSortPass2KeyOf base x y z).lookupVar "n" := by
          simpa [insertionSortPass2AfterJOf] using
            (lookupVar_updateVar_ne (insertionSortPass2KeyOf base x y z) "j" "n" (.int 2)
              (by decide : "n" ≠ "j"))
    _ = (insertionSortAfterPass1Of base x y z).lookupVar "n" := by
          simpa [insertionSortPass2KeyOf] using
            (lookupVar_updateVar_ne (insertionSortAfterPass1Of base x y z) "key" "n" (.int z)
              (by decide : "n" ≠ "key"))
    _ = some (.int 3) := insertionSortAfterPass1_lookup_n base x y z

private theorem insertionSortPass2AfterHi_lookup_i (base : Nat) (x y z : Int) :
    (insertionSortPass2AfterHiOf base x y z).lookupVar "i" = some (.int 3) := by
  simpa [insertionSortPass2AfterHiOf] using
    (lookupVar_updateVar_eq (insertionSortPass2AfterHiWritebackOf base x y z) "i" (.int 3))

private theorem insertionSortPass2AfterHi_eval_outer_cond (base : Nat) (x y z : Int) :
    evalExpr (.binop .lt (.var "i") (.var "n")) (insertionSortPass2AfterHiOf base x y z) =
      some (.int 0) := by
  simp [evalExpr, evalStaticExpr, insertionSortPass2AfterHi_lookup_i base x y z,
    insertionSortPass2AfterHi_lookup_n base x y z]

private theorem insertionSortPass2AfterMid_lookup_a (base : Nat) (x y z : Int) :
    (insertionSortPass2AfterMidOf base x y z).lookupVar "a" = some (.ptr 0 (Int.ofNat base)) := by
  calc
    (insertionSortPass2AfterMidOf base x y z).lookupVar "a"
        = (insertionSortPass2AfterMidWritebackOf base x y z).lookupVar "a" := by
            simpa [insertionSortPass2AfterMidOf] using
              (lookupVar_updateVar_ne (insertionSortPass2AfterMidWritebackOf base x y z) "i" "a" (.int 3)
                (by decide : "a" ≠ "i"))
    _ = (insertionSortPass2AfterMidNoShiftOf base x y z).lookupVar "a" := by
          simp [insertionSortPass2AfterMidWritebackOf, CState.lookupVar]
    _ = some (.ptr 0 (Int.ofNat base)) := insertionSortPass2AfterMidNoShift_lookup_a base x y z

private theorem insertionSortPass2AfterMid_lookup_n (base : Nat) (x y z : Int) :
    (insertionSortPass2AfterMidOf base x y z).lookupVar "n" = some (.int 3) := by
  calc
    (insertionSortPass2AfterMidOf base x y z).lookupVar "n"
        = (insertionSortPass2AfterMidWritebackOf base x y z).lookupVar "n" := by
            simpa [insertionSortPass2AfterMidOf] using
              (lookupVar_updateVar_ne (insertionSortPass2AfterMidWritebackOf base x y z) "i" "n" (.int 3)
                (by decide : "n" ≠ "i"))
    _ = (insertionSortPass2AfterMidNoShiftOf base x y z).lookupVar "n" := by
          simp [insertionSortPass2AfterMidWritebackOf, CState.lookupVar]
    _ = (insertionSortPass2AfterHiShiftOf base x y z).lookupVar "n" := by
          simpa [insertionSortPass2AfterMidNoShiftOf] using
            (lookupVar_updateVar_ne (insertionSortPass2AfterHiShiftOf base x y z) "inserted" "n" (.int 1)
              (by decide : "n" ≠ "inserted"))
    _ = (insertionSortPass2BeforeInnerOf base x y z).lookupVar "n" := by
          calc
            (insertionSortPass2AfterHiShiftOf base x y z).lookupVar "n"
                = (insertionSortPass2AfterHiShiftWriteOf base x y z).lookupVar "n" := by
                    simpa [insertionSortPass2AfterHiShiftOf] using
                      (lookupVar_updateVar_ne (insertionSortPass2AfterHiShiftWriteOf base x y z) "j" "n" (.int 1)
                        (by decide : "n" ≠ "j"))
            _ = (insertionSortPass2BeforeInnerOf base x y z).lookupVar "n" := by
                  simp [insertionSortPass2AfterHiShiftWriteOf, CState.lookupVar]
    _ = (insertionSortPass2AfterJOf base x y z).lookupVar "n" := by
          simpa [insertionSortPass2BeforeInnerOf] using
            (lookupVar_updateVar_ne (insertionSortPass2AfterJOf base x y z) "inserted" "n" (.int 0)
              (by decide : "n" ≠ "inserted"))
    _ = (insertionSortPass2KeyOf base x y z).lookupVar "n" := by
          simpa [insertionSortPass2AfterJOf] using
            (lookupVar_updateVar_ne (insertionSortPass2KeyOf base x y z) "j" "n" (.int 2)
              (by decide : "n" ≠ "j"))
    _ = (insertionSortAfterPass1Of base x y z).lookupVar "n" := by
          simpa [insertionSortPass2KeyOf] using
            (lookupVar_updateVar_ne (insertionSortAfterPass1Of base x y z) "key" "n" (.int z)
              (by decide : "n" ≠ "key"))
    _ = some (.int 3) := insertionSortAfterPass1_lookup_n base x y z

private theorem insertionSortPass2AfterMid_lookup_i (base : Nat) (x y z : Int) :
    (insertionSortPass2AfterMidOf base x y z).lookupVar "i" = some (.int 3) := by
  simpa [insertionSortPass2AfterMidOf] using
    (lookupVar_updateVar_eq (insertionSortPass2AfterMidWritebackOf base x y z) "i" (.int 3))

private theorem insertionSortPass2AfterMid_eval_outer_cond (base : Nat) (x y z : Int) :
    evalExpr (.binop .lt (.var "i") (.var "n")) (insertionSortPass2AfterMidOf base x y z) =
      some (.int 0) := by
  simp [evalExpr, evalStaticExpr, insertionSortPass2AfterMid_lookup_i base x y z,
    insertionSortPass2AfterMid_lookup_n base x y z]

private theorem insertionSortPass2AfterLo_lookup_a (base : Nat) (x y z : Int) :
    (insertionSortPass2AfterLoOf base x y z).lookupVar "a" = some (.ptr 0 (Int.ofNat base)) := by
  calc
    (insertionSortPass2AfterLoOf base x y z).lookupVar "a"
        = (insertionSortPass2AfterLoWritebackOf base x y z).lookupVar "a" := by
            simpa [insertionSortPass2AfterLoOf] using
              (lookupVar_updateVar_ne (insertionSortPass2AfterLoWritebackOf base x y z) "i" "a" (.int 3)
                (by decide : "a" ≠ "i"))
    _ = (insertionSortPass2AfterLoShiftOf base x y z).lookupVar "a" := by
          simp [insertionSortPass2AfterLoWritebackOf, CState.lookupVar]
    _ = some (.ptr 0 (Int.ofNat base)) := insertionSortPass2AfterLoShift_lookup_a base x y z

private theorem insertionSortPass2AfterLo_lookup_n (base : Nat) (x y z : Int) :
    (insertionSortPass2AfterLoOf base x y z).lookupVar "n" = some (.int 3) := by
  calc
    (insertionSortPass2AfterLoOf base x y z).lookupVar "n"
        = (insertionSortPass2AfterLoWritebackOf base x y z).lookupVar "n" := by
            simpa [insertionSortPass2AfterLoOf] using
              (lookupVar_updateVar_ne (insertionSortPass2AfterLoWritebackOf base x y z) "i" "n" (.int 3)
                (by decide : "n" ≠ "i"))
    _ = (insertionSortPass2AfterLoShiftOf base x y z).lookupVar "n" := by
          simp [insertionSortPass2AfterLoWritebackOf, CState.lookupVar]
    _ = (insertionSortPass2AfterHiShiftOf base x y z).lookupVar "n" := by
          calc
            (insertionSortPass2AfterLoShiftOf base x y z).lookupVar "n"
                = (insertionSortPass2AfterLoShiftWriteOf base x y z).lookupVar "n" := by
                    simpa [insertionSortPass2AfterLoShiftOf] using
                      (lookupVar_updateVar_ne (insertionSortPass2AfterLoShiftWriteOf base x y z) "j" "n" (.int 0)
                        (by decide : "n" ≠ "j"))
            _ = (insertionSortPass2AfterHiShiftOf base x y z).lookupVar "n" := by
                  simp [insertionSortPass2AfterLoShiftWriteOf, CState.lookupVar]
    _ = (insertionSortPass2BeforeInnerOf base x y z).lookupVar "n" := by
          calc
            (insertionSortPass2AfterHiShiftOf base x y z).lookupVar "n"
                = (insertionSortPass2AfterHiShiftWriteOf base x y z).lookupVar "n" := by
                    simpa [insertionSortPass2AfterHiShiftOf] using
                      (lookupVar_updateVar_ne (insertionSortPass2AfterHiShiftWriteOf base x y z) "j" "n" (.int 1)
                        (by decide : "n" ≠ "j"))
            _ = (insertionSortPass2BeforeInnerOf base x y z).lookupVar "n" := by
                  simp [insertionSortPass2AfterHiShiftWriteOf, CState.lookupVar]
    _ = (insertionSortPass2AfterJOf base x y z).lookupVar "n" := by
          simpa [insertionSortPass2BeforeInnerOf] using
            (lookupVar_updateVar_ne (insertionSortPass2AfterJOf base x y z) "inserted" "n" (.int 0)
              (by decide : "n" ≠ "inserted"))
    _ = (insertionSortPass2KeyOf base x y z).lookupVar "n" := by
          simpa [insertionSortPass2AfterJOf] using
            (lookupVar_updateVar_ne (insertionSortPass2KeyOf base x y z) "j" "n" (.int 2)
              (by decide : "n" ≠ "j"))
    _ = (insertionSortAfterPass1Of base x y z).lookupVar "n" := by
          simpa [insertionSortPass2KeyOf] using
            (lookupVar_updateVar_ne (insertionSortAfterPass1Of base x y z) "key" "n" (.int z)
              (by decide : "n" ≠ "key"))
    _ = some (.int 3) := insertionSortAfterPass1_lookup_n base x y z

private theorem insertionSortPass2AfterLo_lookup_i (base : Nat) (x y z : Int) :
    (insertionSortPass2AfterLoOf base x y z).lookupVar "i" = some (.int 3) := by
  simpa [insertionSortPass2AfterLoOf] using
    (lookupVar_updateVar_eq (insertionSortPass2AfterLoWritebackOf base x y z) "i" (.int 3))

private theorem insertionSortPass2AfterLo_eval_outer_cond (base : Nat) (x y z : Int) :
    evalExpr (.binop .lt (.var "i") (.var "n")) (insertionSortPass2AfterLoOf base x y z) =
      some (.int 0) := by
  simp [evalExpr, evalStaticExpr, insertionSortPass2AfterLo_lookup_i base x y z,
    insertionSortPass2AfterLo_lookup_n base x y z]

private theorem insertionSortPass2AfterHi_array3At (base : Nat) (x y z : Int)
    (hz : ¬ z < sort2Hi x y) :
    array3At_s base (sort3Lo x y z) (sort3Mid x y z) (sort3Hi x y z)
      (insertionSortPass2AfterHiOf base x y z) := by
  have h0 :
      (insertionSortPass2AfterHiOf base x y z).heap.read base = some (.int (sort2Lo x y)) := by
    calc
      (insertionSortPass2AfterHiOf base x y z).heap.read base
          = (insertionSortPass2AfterHiNoShiftOf base x y z).heap.read base := by
              simp [insertionSortPass2AfterHiOf, insertionSortPass2AfterHiWritebackOf, CState.updateVar]
      _ = (insertionSortAfterPass1Of base x y z).heap.read base := by
            simp [insertionSortPass2AfterHiNoShiftOf, insertionSortPass2BeforeInnerOf,
              insertionSortPass2AfterJOf, insertionSortPass2KeyOf, CState.updateVar]
      _ = some (.int (sort2Lo x y)) := insertionSortAfterPass1_read_base base x y z
  have h1 :
      (insertionSortPass2AfterHiOf base x y z).heap.read (base + 1) = some (.int (sort2Hi x y)) := by
    calc
      (insertionSortPass2AfterHiOf base x y z).heap.read (base + 1)
          = (insertionSortPass2AfterHiNoShiftOf base x y z).heap.read (base + 1) := by
              simp [insertionSortPass2AfterHiOf, insertionSortPass2AfterHiWritebackOf, CState.updateVar]
      _ = (insertionSortAfterPass1Of base x y z).heap.read (base + 1) := by
            simp [insertionSortPass2AfterHiNoShiftOf, insertionSortPass2BeforeInnerOf,
              insertionSortPass2AfterJOf, insertionSortPass2KeyOf, CState.updateVar]
      _ = some (.int (sort2Hi x y)) := insertionSortAfterPass1_read_base_add1 base x y z
  have h2 :
      (insertionSortPass2AfterHiOf base x y z).heap.read (base + 2) = some (.int z) := by
    simp [insertionSortPass2AfterHiOf, insertionSortPass2AfterHiWritebackOf]
  have hzLo : ¬ z < sort2Lo x y := by
    intro hz'
    exact hz (lt_of_lt_of_le hz' (sort2Lo_le_sort2Hi x y))
  simpa [array3At_s, sort3Lo, sort3Mid, sort3Hi, hz, hzLo] using And.intro h0 (And.intro h1 h2)

private theorem insertionSortPass2AfterMid_array3At (base : Nat) (x y z : Int)
    (hzHi : z < sort2Hi x y) (hzLo : ¬ z < sort2Lo x y) :
    array3At_s base (sort3Lo x y z) (sort3Mid x y z) (sort3Hi x y z)
      (insertionSortPass2AfterMidOf base x y z) := by
  have h0 :
      (insertionSortPass2AfterMidOf base x y z).heap.read base = some (.int (sort2Lo x y)) := by
    calc
      (insertionSortPass2AfterMidOf base x y z).heap.read base
          = (insertionSortPass2AfterMidNoShiftOf base x y z).heap.read base := by
              simp [insertionSortPass2AfterMidOf, insertionSortPass2AfterMidWritebackOf, CState.updateVar]
      _ = (insertionSortPass2AfterHiShiftOf base x y z).heap.read base := by
            simp [insertionSortPass2AfterMidNoShiftOf, CState.updateVar]
      _ = (insertionSortAfterPass1Of base x y z).heap.read base := by
            simp [insertionSortPass2AfterHiShiftOf, insertionSortPass2AfterHiShiftWriteOf,
              insertionSortPass2BeforeInnerOf, insertionSortPass2AfterJOf, insertionSortPass2KeyOf,
              CState.updateVar]
      _ = some (.int (sort2Lo x y)) := insertionSortAfterPass1_read_base base x y z
  have h1 :
      (insertionSortPass2AfterMidOf base x y z).heap.read (base + 1) = some (.int z) := by
    simp [insertionSortPass2AfterMidOf, insertionSortPass2AfterMidWritebackOf]
  have h2 :
      (insertionSortPass2AfterMidOf base x y z).heap.read (base + 2) = some (.int (sort2Hi x y)) := by
    calc
      (insertionSortPass2AfterMidOf base x y z).heap.read (base + 2)
          = (insertionSortPass2AfterMidNoShiftOf base x y z).heap.read (base + 2) := by
              simp [insertionSortPass2AfterMidOf, insertionSortPass2AfterMidWritebackOf, CState.updateVar]
      _ = (insertionSortPass2AfterHiShiftOf base x y z).heap.read (base + 2) := by
            simp [insertionSortPass2AfterMidNoShiftOf, CState.updateVar]
      _ = some (.int (sort2Hi x y)) := by
            simp [insertionSortPass2AfterHiShiftOf, insertionSortPass2AfterHiShiftWriteOf]
  simpa [array3At_s, sort3Lo, sort3Mid, sort3Hi, hzHi, hzLo] using And.intro h0 (And.intro h1 h2)

private theorem insertionSortPass2AfterLo_array3At (base : Nat) (x y z : Int)
    (hzHi : z < sort2Hi x y) (hzLo : z < sort2Lo x y) :
    array3At_s base (sort3Lo x y z) (sort3Mid x y z) (sort3Hi x y z)
      (insertionSortPass2AfterLoOf base x y z) := by
  have h0 :
      (insertionSortPass2AfterLoOf base x y z).heap.read base = some (.int z) := by
    simp [insertionSortPass2AfterLoOf, insertionSortPass2AfterLoWritebackOf]
  have h1 :
      (insertionSortPass2AfterLoOf base x y z).heap.read (base + 1) = some (.int (sort2Lo x y)) := by
    calc
      (insertionSortPass2AfterLoOf base x y z).heap.read (base + 1)
          = (insertionSortPass2AfterLoShiftOf base x y z).heap.read (base + 1) := by
              simp [insertionSortPass2AfterLoOf, insertionSortPass2AfterLoWritebackOf]
      _ = some (.int (sort2Lo x y)) := by
            simp [insertionSortPass2AfterLoShiftOf, insertionSortPass2AfterLoShiftWriteOf]
  have h2 :
      (insertionSortPass2AfterLoOf base x y z).heap.read (base + 2) = some (.int (sort2Hi x y)) := by
    calc
      (insertionSortPass2AfterLoOf base x y z).heap.read (base + 2)
          = (insertionSortPass2AfterLoShiftOf base x y z).heap.read (base + 2) := by
              simp [insertionSortPass2AfterLoOf, insertionSortPass2AfterLoWritebackOf]
      _ = (insertionSortPass2AfterHiShiftOf base x y z).heap.read (base + 2) := by
            simp [insertionSortPass2AfterLoShiftOf, insertionSortPass2AfterLoShiftWriteOf]
      _ = some (.int (sort2Hi x y)) := by
            simp [insertionSortPass2AfterHiShiftOf, insertionSortPass2AfterHiShiftWriteOf]
  simpa [array3At_s, sort3Lo, sort3Mid, sort3Hi, hzHi, hzLo] using And.intro h0 (And.intro h1 h2)

private theorem insertionSort_ret_hi_exec_of (base : Nat) (x y z : Int)
    (hz : ¬ z < sort2Hi x y) :
    execStmt 28 (.ret (.arrayAccess (.var "a") (.intLit 0))) (insertionSortPass2AfterHiOf base x y z) =
      some (.returned (.int (sort3Lo x y z)) (insertionSortPass2AfterHiOf base x y z)) := by
  have ha := insertionSortPass2AfterHi_lookup_a base x y z
  have hRead :
      (insertionSortPass2AfterHiOf base x y z).heap.read base = some (.int (sort3Lo x y z)) :=
    (insertionSortPass2AfterHi_array3At base x y z hz).1
  have hReadPtr :
      (insertionSortPass2AfterHiOf base x y z).readPtr { block := 0, offset := Int.ofNat base } =
        some (.int (sort3Lo x y z)) := by
    simpa [hRead] using
      (CState.readPtr_block0 (insertionSortPass2AfterHiOf base x y z) base base)
  have hAdd :
      evalBinOp .add (.ptr 0 (Int.ofNat base)) (.int 0) =
        some (CVal.ptr 0 (Int.ofNat base)) := by
    change
      (if 0 ≤ (0 : Int) then
        some (CVal.ptr 0 (Int.ofNat base + 0))
      else none) = some (CVal.ptr 0 (Int.ofNat base))
    simp
  have hEval :
      evalExpr (.arrayAccess (.var "a") (.intLit 0)) (insertionSortPass2AfterHiOf base x y z) =
        some (.int (sort3Lo x y z)) := by
    simp only [evalExpr, evalStaticExpr, ha, hAdd, Option.bind, Bind.bind]; exact hReadPtr
  simp [execStmt, hEval]

private theorem insertionSort_ret_mid_exec_of (base : Nat) (x y z : Int)
    (hzHi : z < sort2Hi x y) (hzLo : ¬ z < sort2Lo x y) :
    execStmt 28 (.ret (.arrayAccess (.var "a") (.intLit 0))) (insertionSortPass2AfterMidOf base x y z) =
      some (.returned (.int (sort3Lo x y z)) (insertionSortPass2AfterMidOf base x y z)) := by
  have ha := insertionSortPass2AfterMid_lookup_a base x y z
  have hRead :
      (insertionSortPass2AfterMidOf base x y z).heap.read base = some (.int (sort3Lo x y z)) :=
    (insertionSortPass2AfterMid_array3At base x y z hzHi hzLo).1
  have hReadPtr :
      (insertionSortPass2AfterMidOf base x y z).readPtr { block := 0, offset := Int.ofNat base } =
        some (.int (sort3Lo x y z)) := by
    simpa [hRead] using
      (CState.readPtr_block0 (insertionSortPass2AfterMidOf base x y z) base base)
  have hAdd :
      evalBinOp .add (.ptr 0 (Int.ofNat base)) (.int 0) =
        some (CVal.ptr 0 (Int.ofNat base)) := by
    change
      (if 0 ≤ (0 : Int) then
        some (CVal.ptr 0 (Int.ofNat base + 0))
      else none) = some (CVal.ptr 0 (Int.ofNat base))
    simp
  have hEval :
      evalExpr (.arrayAccess (.var "a") (.intLit 0)) (insertionSortPass2AfterMidOf base x y z) =
        some (.int (sort3Lo x y z)) := by
    simp only [evalExpr, evalStaticExpr, ha, hAdd, Option.bind, Bind.bind]; exact hReadPtr
  simp [execStmt, hEval]

private theorem insertionSort_ret_lo_exec_of (base : Nat) (x y z : Int)
    (hzHi : z < sort2Hi x y) (hzLo : z < sort2Lo x y) :
    execStmt 28 (.ret (.arrayAccess (.var "a") (.intLit 0))) (insertionSortPass2AfterLoOf base x y z) =
      some (.returned (.int (sort3Lo x y z)) (insertionSortPass2AfterLoOf base x y z)) := by
  have ha := insertionSortPass2AfterLo_lookup_a base x y z
  have hRead :
      (insertionSortPass2AfterLoOf base x y z).heap.read base = some (.int (sort3Lo x y z)) :=
    (insertionSortPass2AfterLo_array3At base x y z hzHi hzLo).1
  have hReadPtr :
      (insertionSortPass2AfterLoOf base x y z).readPtr { block := 0, offset := Int.ofNat base } =
        some (.int (sort3Lo x y z)) := by
    simpa [hRead] using
      (CState.readPtr_block0 (insertionSortPass2AfterLoOf base x y z) base base)
  have hAdd :
      evalBinOp .add (.ptr 0 (Int.ofNat base)) (.int 0) =
        some (CVal.ptr 0 (Int.ofNat base)) := by
    change
      (if 0 ≤ (0 : Int) then
        some (CVal.ptr 0 (Int.ofNat base + 0))
      else none) = some (CVal.ptr 0 (Int.ofNat base))
    simp
  have hEval :
      evalExpr (.arrayAccess (.var "a") (.intLit 0)) (insertionSortPass2AfterLoOf base x y z) =
        some (.int (sort3Lo x y z)) := by
    simp only [evalExpr, evalStaticExpr, ha, hAdd, Option.bind, Bind.bind]; exact hReadPtr
  simp [execStmt, hEval]

private theorem insertionSort_outer_pass1_exec_of (base : Nat) (x y z : Int) :
    execStmt 27 insertionOuterBody (insertionSortAfterInitOf base x y z) =
      some (.normal (insertionSortAfterPass1Of base x y z)) := by
  simp [insertionOuterBody, execStmt]
  have hKey :
      ((evalExpr (.arrayAccess (.var "a") (.var "i")) (insertionSortAfterInitOf base x y z)).bind
        fun v => some (ExecResult.normal ((insertionSortAfterInitOf base x y z).updateVar "key" v))) =
        some (.normal (insertionSortAfterKeyOf base x y z)) := by
    simpa [execStmt] using insertionSort_assign_key_exec_of 26 base x y z
  rw [hKey]
  simp [execStmt]
  have hJ :
      ((insertionSortAfterKeyOf base x y z).lookupVar "i").bind
        (fun v => some (ExecResult.normal ((insertionSortAfterKeyOf base x y z).updateVar "j" v))) =
        some (.normal (insertionSortAfterJOf base x y z)) := by
    simpa [execStmt] using insertionSort_assign_j_exec_of 25 base x y z
  rw [hJ]
  simp [execStmt]
  have hInserted :
      ((evalExpr (.intLit 0) (insertionSortAfterJOf base x y z)).bind
        fun v => some (ExecResult.normal ((insertionSortAfterJOf base x y z).updateVar "inserted" v))) =
        some (.normal (insertionSortBeforeInnerOf base x y z)) := by
    simpa [execStmt] using insertionSort_assign_inserted_exec_of 24 base x y z
  rw [hInserted]
  simpa using insertionSort_pass1_correct 18 base x y z

private theorem insertionSort_outer_pass2_hi_exec_of (base : Nat) (x y z : Int)
    (hz : ¬ z < sort2Hi x y) :
    execStmt 26 insertionOuterBody (insertionSortAfterPass1Of base x y z) =
      some (.normal (insertionSortPass2AfterHiOf base x y z)) := by
  simp [insertionOuterBody, execStmt]
  have hKey :
      ((evalExpr (.arrayAccess (.var "a") (.var "i")) (insertionSortAfterPass1Of base x y z)).bind
        fun v => some (ExecResult.normal ((insertionSortAfterPass1Of base x y z).updateVar "key" v))) =
        some (.normal (insertionSortPass2KeyOf base x y z)) := by
    simpa [execStmt] using insertionSort_pass2_assign_key_exec_of 25 base x y z
  rw [hKey]
  simp [execStmt]
  have hJ :
      ((insertionSortPass2KeyOf base x y z).lookupVar "i").bind
        (fun v => some (ExecResult.normal ((insertionSortPass2KeyOf base x y z).updateVar "j" v))) =
        some (.normal (insertionSortPass2AfterJOf base x y z)) := by
    simpa [execStmt] using insertionSort_pass2_assign_j_exec_of 24 base x y z
  rw [hJ]
  simp [execStmt]
  have hInserted :
      ((evalExpr (.intLit 0) (insertionSortPass2AfterJOf base x y z)).bind
        fun v => some (ExecResult.normal ((insertionSortPass2AfterJOf base x y z).updateVar "inserted" v))) =
        some (.normal (insertionSortPass2BeforeInnerOf base x y z)) := by
    simpa [execStmt] using insertionSort_pass2_assign_inserted_exec_of 23 base x y z
  rw [hInserted]
  simpa using insertionSort_pass2_hi_exec_of 17 base x y z hz

private theorem insertionSort_outer_pass2_mid_exec_of (base : Nat) (x y z : Int)
    (hzHi : z < sort2Hi x y) (hzLo : ¬ z < sort2Lo x y) :
    execStmt 26 insertionOuterBody (insertionSortAfterPass1Of base x y z) =
      some (.normal (insertionSortPass2AfterMidOf base x y z)) := by
  simp [insertionOuterBody, execStmt]
  have hKey :
      ((evalExpr (.arrayAccess (.var "a") (.var "i")) (insertionSortAfterPass1Of base x y z)).bind
        fun v => some (ExecResult.normal ((insertionSortAfterPass1Of base x y z).updateVar "key" v))) =
        some (.normal (insertionSortPass2KeyOf base x y z)) := by
    simpa [execStmt] using insertionSort_pass2_assign_key_exec_of 25 base x y z
  rw [hKey]
  simp [execStmt]
  have hJ :
      ((insertionSortPass2KeyOf base x y z).lookupVar "i").bind
        (fun v => some (ExecResult.normal ((insertionSortPass2KeyOf base x y z).updateVar "j" v))) =
        some (.normal (insertionSortPass2AfterJOf base x y z)) := by
    simpa [execStmt] using insertionSort_pass2_assign_j_exec_of 24 base x y z
  rw [hJ]
  simp [execStmt]
  have hInserted :
      ((evalExpr (.intLit 0) (insertionSortPass2AfterJOf base x y z)).bind
        fun v => some (ExecResult.normal ((insertionSortPass2AfterJOf base x y z).updateVar "inserted" v))) =
        some (.normal (insertionSortPass2BeforeInnerOf base x y z)) := by
    simpa [execStmt] using insertionSort_pass2_assign_inserted_exec_of 23 base x y z
  rw [hInserted]
  simpa using insertionSort_pass2_mid_exec_of 14 base x y z hzHi hzLo

private theorem insertionSort_outer_pass2_low_exec_of (base : Nat) (x y z : Int)
    (hzHi : z < sort2Hi x y) (hzLo : z < sort2Lo x y) :
    execStmt 26 insertionOuterBody (insertionSortAfterPass1Of base x y z) =
      some (.normal (insertionSortPass2AfterLoOf base x y z)) := by
  simp [insertionOuterBody, execStmt]
  have hKey :
      ((evalExpr (.arrayAccess (.var "a") (.var "i")) (insertionSortAfterPass1Of base x y z)).bind
        fun v => some (ExecResult.normal ((insertionSortAfterPass1Of base x y z).updateVar "key" v))) =
        some (.normal (insertionSortPass2KeyOf base x y z)) := by
    simpa [execStmt] using insertionSort_pass2_assign_key_exec_of 25 base x y z
  rw [hKey]
  simp [execStmt]
  have hJ :
      ((insertionSortPass2KeyOf base x y z).lookupVar "i").bind
        (fun v => some (ExecResult.normal ((insertionSortPass2KeyOf base x y z).updateVar "j" v))) =
        some (.normal (insertionSortPass2AfterJOf base x y z)) := by
    simpa [execStmt] using insertionSort_pass2_assign_j_exec_of 24 base x y z
  rw [hJ]
  simp [execStmt]
  have hInserted :
      ((evalExpr (.intLit 0) (insertionSortPass2AfterJOf base x y z)).bind
        fun v => some (ExecResult.normal ((insertionSortPass2AfterJOf base x y z).updateVar "inserted" v))) =
        some (.normal (insertionSortPass2BeforeInnerOf base x y z)) := by
    simpa [execStmt] using insertionSort_pass2_assign_inserted_exec_of 23 base x y z
  rw [hInserted]
  simpa using insertionSort_pass2_low_exec_of 14 base x y z hzHi hzLo

private theorem insertionSort_branch_hi_correct (base : Nat) (x y z : Int)
    (hz : ¬ z < sort2Hi x y) :
    ∃ st',
      execStmt 30 insertionSortBody (insertionSortInitOf base x y z) =
        some (.returned (.int (sort3Lo x y z)) st') ∧
      array3At_s base (sort3Lo x y z) (sort3Mid x y z) (sort3Hi x y z) st' := by
  refine ⟨insertionSortPass2AfterHiOf base x y z, ?_, insertionSortPass2AfterHi_array3At base x y z hz⟩
  rw [show execStmt 30 insertionSortBody (insertionSortInitOf base x y z) =
      execStmt 30
        (.seq (.assign (.var "i") (.intLit 1))
          (.seq (.whileInv (.binop .lt (.var "i") (.var "n")) HProp.htrue insertionOuterBody)
            (.ret (.arrayAccess (.var "a") (.intLit 0)))))
        (insertionSortInitOf base x y z) by rfl]
  rw [execStmt_seq_of_normal (fuel := 29)
        (s1 := (.assign (.var "i") (.intLit 1)))
        (s2 := (.seq (.whileInv (.binop .lt (.var "i") (.var "n")) HProp.htrue insertionOuterBody)
          (.ret (.arrayAccess (.var "a") (.intLit 0)))))
        (st := insertionSortInitOf base x y z)
        (st' := insertionSortAfterInitOf base x y z)
        (h := insertionSort_seed_executes_of base x y z)]
  rw [execStmt_seq_of_normal (fuel := 28)
        (s1 := (.whileInv (.binop .lt (.var "i") (.var "n")) HProp.htrue insertionOuterBody))
        (s2 := (.ret (.arrayAccess (.var "a") (.intLit 0))))
        (st := insertionSortAfterInitOf base x y z)
        (st' := insertionSortPass2AfterHiOf base x y z)
        (h := by
          rw [execStmt_whileInv_of_eval_true_normal (fuel := 27)
                (cond := (.binop .lt (.var "i") (.var "n"))) (inv := HProp.htrue)
                (body := insertionOuterBody) (st := insertionSortAfterInitOf base x y z)
                (st' := insertionSortAfterPass1Of base x y z) (v := .int 1)
                (hEval := insertionSortAfterInit_eval_outer_cond base x y z)
                (hTruth := by simp [isTruthy])
                (hBody := insertionSort_outer_pass1_exec_of base x y z)]
          rw [execStmt_whileInv_of_eval_true_normal (fuel := 26)
                (cond := (.binop .lt (.var "i") (.var "n"))) (inv := HProp.htrue)
                (body := insertionOuterBody) (st := insertionSortAfterPass1Of base x y z)
                (st' := insertionSortPass2AfterHiOf base x y z) (v := .int 1)
                (hEval := insertionSortAfterPass1_eval_outer_cond base x y z)
                (hTruth := by simp [isTruthy])
                (hBody := insertionSort_outer_pass2_hi_exec_of base x y z hz)]
          exact execStmt_whileInv_of_eval_false (fuel := 25)
            (cond := (.binop .lt (.var "i") (.var "n"))) (inv := HProp.htrue)
            (body := insertionOuterBody) (st := insertionSortPass2AfterHiOf base x y z)
            (v := .int 0) (hEval := insertionSortPass2AfterHi_eval_outer_cond base x y z)
            (hTruth := by simp [isTruthy]))]
  exact insertionSort_ret_hi_exec_of base x y z hz

private theorem insertionSort_branch_mid_correct (base : Nat) (x y z : Int)
    (hzHi : z < sort2Hi x y) (hzLo : ¬ z < sort2Lo x y) :
    ∃ st',
      execStmt 30 insertionSortBody (insertionSortInitOf base x y z) =
        some (.returned (.int (sort3Lo x y z)) st') ∧
      array3At_s base (sort3Lo x y z) (sort3Mid x y z) (sort3Hi x y z) st' := by
  refine ⟨insertionSortPass2AfterMidOf base x y z, ?_, insertionSortPass2AfterMid_array3At base x y z hzHi hzLo⟩
  rw [show execStmt 30 insertionSortBody (insertionSortInitOf base x y z) =
      execStmt 30
        (.seq (.assign (.var "i") (.intLit 1))
          (.seq (.whileInv (.binop .lt (.var "i") (.var "n")) HProp.htrue insertionOuterBody)
            (.ret (.arrayAccess (.var "a") (.intLit 0)))))
        (insertionSortInitOf base x y z) by rfl]
  rw [execStmt_seq_of_normal (fuel := 29)
        (s1 := (.assign (.var "i") (.intLit 1)))
        (s2 := (.seq (.whileInv (.binop .lt (.var "i") (.var "n")) HProp.htrue insertionOuterBody)
          (.ret (.arrayAccess (.var "a") (.intLit 0)))))
        (st := insertionSortInitOf base x y z)
        (st' := insertionSortAfterInitOf base x y z)
        (h := insertionSort_seed_executes_of base x y z)]
  rw [execStmt_seq_of_normal (fuel := 28)
        (s1 := (.whileInv (.binop .lt (.var "i") (.var "n")) HProp.htrue insertionOuterBody))
        (s2 := (.ret (.arrayAccess (.var "a") (.intLit 0))))
        (st := insertionSortAfterInitOf base x y z)
        (st' := insertionSortPass2AfterMidOf base x y z)
        (h := by
          rw [execStmt_whileInv_of_eval_true_normal (fuel := 27)
                (cond := (.binop .lt (.var "i") (.var "n"))) (inv := HProp.htrue)
                (body := insertionOuterBody) (st := insertionSortAfterInitOf base x y z)
                (st' := insertionSortAfterPass1Of base x y z) (v := .int 1)
                (hEval := insertionSortAfterInit_eval_outer_cond base x y z)
                (hTruth := by simp [isTruthy])
                (hBody := insertionSort_outer_pass1_exec_of base x y z)]
          rw [execStmt_whileInv_of_eval_true_normal (fuel := 26)
                (cond := (.binop .lt (.var "i") (.var "n"))) (inv := HProp.htrue)
                (body := insertionOuterBody) (st := insertionSortAfterPass1Of base x y z)
                (st' := insertionSortPass2AfterMidOf base x y z) (v := .int 1)
                (hEval := insertionSortAfterPass1_eval_outer_cond base x y z)
                (hTruth := by simp [isTruthy])
                (hBody := insertionSort_outer_pass2_mid_exec_of base x y z hzHi hzLo)]
          exact execStmt_whileInv_of_eval_false (fuel := 25)
            (cond := (.binop .lt (.var "i") (.var "n"))) (inv := HProp.htrue)
            (body := insertionOuterBody) (st := insertionSortPass2AfterMidOf base x y z)
            (v := .int 0) (hEval := insertionSortPass2AfterMid_eval_outer_cond base x y z)
            (hTruth := by simp [isTruthy]))]
  exact insertionSort_ret_mid_exec_of base x y z hzHi hzLo

private theorem insertionSort_branch_low_correct (base : Nat) (x y z : Int)
    (hzHi : z < sort2Hi x y) (hzLo : z < sort2Lo x y) :
    ∃ st',
      execStmt 30 insertionSortBody (insertionSortInitOf base x y z) =
        some (.returned (.int (sort3Lo x y z)) st') ∧
      array3At_s base (sort3Lo x y z) (sort3Mid x y z) (sort3Hi x y z) st' := by
  refine ⟨insertionSortPass2AfterLoOf base x y z, ?_, insertionSortPass2AfterLo_array3At base x y z hzHi hzLo⟩
  rw [show execStmt 30 insertionSortBody (insertionSortInitOf base x y z) =
      execStmt 30
        (.seq (.assign (.var "i") (.intLit 1))
          (.seq (.whileInv (.binop .lt (.var "i") (.var "n")) HProp.htrue insertionOuterBody)
            (.ret (.arrayAccess (.var "a") (.intLit 0)))))
        (insertionSortInitOf base x y z) by rfl]
  rw [execStmt_seq_of_normal (fuel := 29)
        (s1 := (.assign (.var "i") (.intLit 1)))
        (s2 := (.seq (.whileInv (.binop .lt (.var "i") (.var "n")) HProp.htrue insertionOuterBody)
          (.ret (.arrayAccess (.var "a") (.intLit 0)))))
        (st := insertionSortInitOf base x y z)
        (st' := insertionSortAfterInitOf base x y z)
        (h := insertionSort_seed_executes_of base x y z)]
  rw [execStmt_seq_of_normal (fuel := 28)
        (s1 := (.whileInv (.binop .lt (.var "i") (.var "n")) HProp.htrue insertionOuterBody))
        (s2 := (.ret (.arrayAccess (.var "a") (.intLit 0))))
        (st := insertionSortAfterInitOf base x y z)
        (st' := insertionSortPass2AfterLoOf base x y z)
        (h := by
          rw [execStmt_whileInv_of_eval_true_normal (fuel := 27)
                (cond := (.binop .lt (.var "i") (.var "n"))) (inv := HProp.htrue)
                (body := insertionOuterBody) (st := insertionSortAfterInitOf base x y z)
                (st' := insertionSortAfterPass1Of base x y z) (v := .int 1)
                (hEval := insertionSortAfterInit_eval_outer_cond base x y z)
                (hTruth := by simp [isTruthy])
                (hBody := insertionSort_outer_pass1_exec_of base x y z)]
          rw [execStmt_whileInv_of_eval_true_normal (fuel := 26)
                (cond := (.binop .lt (.var "i") (.var "n"))) (inv := HProp.htrue)
                (body := insertionOuterBody) (st := insertionSortAfterPass1Of base x y z)
                (st' := insertionSortPass2AfterLoOf base x y z) (v := .int 1)
                (hEval := insertionSortAfterPass1_eval_outer_cond base x y z)
                (hTruth := by simp [isTruthy])
                (hBody := insertionSort_outer_pass2_low_exec_of base x y z hzHi hzLo)]
          exact execStmt_whileInv_of_eval_false (fuel := 25)
            (cond := (.binop .lt (.var "i") (.var "n"))) (inv := HProp.htrue)
            (body := insertionOuterBody) (st := insertionSortPass2AfterLoOf base x y z)
            (v := .int 0) (hEval := insertionSortPass2AfterLo_eval_outer_cond base x y z)
            (hTruth := by simp [isTruthy]))]
  exact insertionSort_ret_lo_exec_of base x y z hzHi hzLo

theorem insertionSort_correct (base : Nat) (x y z : Int) :
    ∃ st',
      execStmt 30 insertionSortBody (insertionSortInitOf base x y z) =
        some (.returned (.int (sort3Lo x y z)) st') ∧
      array3At_s base (sort3Lo x y z) (sort3Mid x y z) (sort3Hi x y z) st' := by
  by_cases hzHi : z < sort2Hi x y
  · by_cases hzLo : z < sort2Lo x y
    · exact insertionSort_branch_low_correct base x y z hzHi hzLo
    · exact insertionSort_branch_mid_correct base x y z hzHi hzLo
  · exact insertionSort_branch_hi_correct base x y z hzHi

theorem insertionSort_pass1_executes :
    execStmt 28 insertionOuterBody insertionSortAfterInit =
      some (.normal insertionSortAfterPass1) := by
  native_decide

theorem insertionSort_pass2_executes :
    execStmt 27 insertionOuterBody insertionSortAfterPass1 =
      some (.normal insertionSortFinal) := by
  native_decide

theorem insertionSort_executes :
    execStmt 30 insertionSortBody insertionSortInit =
      some (.returned (.int 1) insertionSortFinal) := by
  native_decide

theorem insertionSort_verified :
    ∃ st',
      execStmt 30 insertionSortBody insertionSortInit =
        some (.returned (.int 1) st') ∧
      st'.heap.read 100 = some (.int 1) ∧
      st'.heap.read 101 = some (.int 2) ∧
      st'.heap.read 102 = some (.int 3) := by
  refine ⟨insertionSortFinal, insertionSort_executes, ?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide

theorem insertionSort_forward_verified :
    swp (.assign (.var "i") (.intLit 1))
      (fun _ st => st.lookupVar "i" = some (.int 1))
      insertionSortInit := by
  simp [swp, insertionSortInit, evalExpr, evalStaticExpr, CState.lookupVar, CState.updateVar]

end HeytingLean.LeanCP.Examples
