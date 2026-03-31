import HeytingLean.LeanCP.Lang.CSyntax
import HeytingLean.LeanCP.Core.Heap

/-!
# LeanCP C Operational Semantics

Big-step operational semantics for the LeanCP C subset, operating over
`(CStmt, Heap, Env)` configurations. Used by the refutation tactic (Phase 7)
and for sanity testing.
-/

namespace HeytingLean.LeanCP

/-- Local variable environment (association list). -/
abbrev Env := List (String × CVal)

/-- Transitional allocation metadata linking legacy flat addresses to fresh
block identifiers in the new `Mem` model. -/
structure FlatAlloc where
  base : Nat
  block : Block
  cells : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Program state: heap + local environment + next free address. -/
structure CState where
  heap : Heap
  env : Env
  nextAddr : Nat
  mem : Mem := heapToMem heap
  allocs : List FlatAlloc := []
  deriving Inhabited

namespace CState

/-- Materialize the contents of a tracked allocation from the legacy heap. -/
def allocContents (h : Heap) (alloc : FlatAlloc) : Finmap (fun _ : Offset => CVal) :=
  (List.range alloc.cells).foldl
    (fun acc i => acc.insert (Int.ofNat i) ((h.read (alloc.base + i)).getD CVal.undef))
    (∅ : Finmap (fun _ : Offset => CVal))

/-- Rebuild the block-memory view from the current heap plus tracked
allocations. Block 0 keeps the legacy compatibility embedding; tracked
allocations are mirrored into their own fresh blocks. -/
def syncMem (heap : Heap) (allocs : List FlatAlloc) (nextBlockHint : Block) : Mem :=
  let baseMem := heapToMem heap
  let blocks :=
    allocs.foldl
      (fun acc alloc =>
        acc.insert alloc.block
          { lo := 0
            hi := Int.ofNat alloc.cells
            contents := allocContents heap alloc
            perm := .Freeable })
      baseMem.blocks
  let maxBlock :=
    allocs.foldl (fun acc alloc => max acc (alloc.block + 1)) nextBlockHint
  { blocks := blocks, nextBlock := max baseMem.nextBlock maxBlock }

/-- Resolve a flat address against the tracked allocation metadata. -/
def resolveAddr (st : CState) (addr : Nat) : Option Addr :=
  st.allocs.findSome? fun alloc =>
    if alloc.base ≤ addr then
      if addr < alloc.base + alloc.cells then
        some { block := alloc.block, offset := Int.ofNat (addr - alloc.base) }
      else
        none
    else
      none

/-- Find the tracked allocation metadata for a native nonzero block id. -/
def findAllocByBlock (st : CState) (block : Block) : Option FlatAlloc :=
  st.allocs.find? (fun alloc => alloc.block = block)

/-- Resolve a native pointer value back to the legacy flat address used by the
current executable heap.

Block 0 remains the explicit legacy-compatibility boundary. For tracked
nonzero blocks, resolution is derived from the allocation metadata rather than
blindly trusting the cached `flat` projection. -/
def resolvePtr (st : CState) (ptr : PtrVal) : Option Nat := do
  if ptr.block = 0 then
    if 0 ≤ ptr.offset then some (Int.toNat ptr.offset) else none
  else
    let alloc ← st.findAllocByBlock ptr.block
    if 0 ≤ ptr.offset then
      let ofs := Int.toNat ptr.offset
      if ofs < alloc.cells then
        some (alloc.base + ofs)
      else
        none
    else
      none

/-- Canonical synchronized heap update for the Phase 1 parallel-track memory
migration. Until pointers stop being flat `Nat`s, the executable semantics keep
the legacy heap as the allocation source of truth and mirror it into `mem`. -/
def withHeap (st : CState) (heap : Heap) : CState :=
  { heap := heap
    env := st.env
    nextAddr := st.nextAddr
    mem := syncMem heap st.allocs st.mem.nextBlock
    allocs := st.allocs }

def lookupVar (st : CState) (x : String) : Option CVal :=
  st.env.lookup x

def removeVar (st : CState) (x : String) : CState :=
  { st with env := st.env.filter (fun p => p.1 != x) }

def updateVar (st : CState) (x : String) (v : CVal) : CState :=
  { st with env := (x, v) :: st.env.filter (fun p => p.1 != x) }

/-- Transitional cell read. The state now tracks real allocation metadata and a
block-memory mirror, but existing proof states throughout LeanCP still treat
the flat heap as authoritative. Until the pointer surface is migrated, reads
stay on the legacy heap. -/
def readCell (st : CState) (addr : Nat) : Option CVal :=
  st.heap.read addr

/-- Transitional pointer read through the native pointer surface. -/
def readPtr (st : CState) (ptr : PtrVal) : Option CVal := do
  let addr ← st.resolvePtr ptr
  st.readCell addr

/-- Transitional pointer write through the native pointer surface. -/
def writePtr (st : CState) (ptr : PtrVal) (v : CVal) : Option CState := do
  let addr ← st.resolvePtr ptr
  some (st.withHeap (st.heap.write addr v))

@[simp] theorem resolvePtr_block0 (st : CState) (flat ofs : Nat) :
    st.resolvePtr { block := 0, offset := Int.ofNat flat } = some flat := by
  simp [CState.resolvePtr]

theorem resolvePtr_tracked (st : CState) (alloc : FlatAlloc) (ofs : Nat)
    (halloc : st.findAllocByBlock alloc.block = some alloc)
    (hblock : alloc.block ≠ 0)
    (hofs : ofs < alloc.cells) :
    st.resolvePtr { block := alloc.block, offset := Int.ofNat ofs } =
      some (alloc.base + ofs) := by
  simp [CState.resolvePtr, hblock]
  rw [halloc]
  simp [hofs]

@[simp] theorem readPtr_block0 (st : CState) (flat ofs : Nat) :
    st.readPtr { block := 0, offset := Int.ofNat flat } = st.heap.read flat := by
  simp [CState.readPtr, CState.resolvePtr, CState.readCell]

@[simp] theorem writePtr_block0 (st : CState) (flat ofs : Nat) (v : CVal) :
    st.writePtr { block := 0, offset := Int.ofNat flat } v =
      some (st.withHeap (st.heap.write flat v)) := by
  simp [CState.writePtr, CState.resolvePtr]

@[simp] theorem readCell_eq_heap_read (st : CState) (addr : Nat) :
    st.readCell addr = st.heap.read addr := by
  simp [CState.readCell]

@[simp] theorem withHeap_heap (st : CState) (heap : Heap) :
    (st.withHeap heap).heap = heap := by
  rfl

@[simp] theorem withHeap_env (st : CState) (heap : Heap) :
    (st.withHeap heap).env = st.env := by
  rfl

@[simp] theorem withHeap_nextAddr (st : CState) (heap : Heap) :
    (st.withHeap heap).nextAddr = st.nextAddr := by
  rfl

@[simp] theorem withHeap_mem (st : CState) (heap : Heap) :
    (st.withHeap heap).mem = syncMem heap st.allocs st.mem.nextBlock := by
  rfl

@[simp] theorem withHeap_allocs (st : CState) (heap : Heap) :
    (st.withHeap heap).allocs = st.allocs := by
  rfl

@[simp] theorem updateVar_withHeap (st : CState) (heap : Heap) (x : String) (v : CVal) :
    (st.withHeap heap).updateVar x v = (st.updateVar x v).withHeap heap := by
  cases st
  rfl

end CState

/-- Enter a block by declaring each local as `undef`. -/
def enterBlockState (st : CState) (decls : List (String × CType)) : CState :=
  decls.foldl (fun acc decl => acc.updateVar decl.1 CVal.undef) st

/-- Restore the bindings of block-local names after the block finishes while
keeping the resulting heap and allocator state. -/
def restoreBlockState (before after : CState) (decls : List (String × CType)) : CState :=
  decls.foldl
    (fun acc decl =>
      match before.lookupVar decl.1 with
      | some v => acc.updateVar decl.1 v
      | none => acc.removeVar decl.1)
    after

/-- Evaluate an expression to a value. Static expressions are delegated to the
shared evaluator so literal/binop behavior stays aligned with WP. -/
def evalExpr (e : CExpr) (st : CState) : Option CVal :=
  match evalStaticExpr e with
  | some v => some v
  | none =>
      match e with
      | .var x => st.lookupVar x
      | .sizeOf ty => some (.int (Int.ofNat (typeSize ty)))
      | .cast ty e' => do
          let v ← evalExpr e' st
          match ty, v with
          | .int, .int n => some (.int n)
          | .intSized .Signed sz, .int n => some (.int (wrapSignedInt sz n))
          | .intSized .Unsigned sz, .int n => some (.uint (wrapUnsignedNat sz n) sz)
          | .int, .uint n _ => some (.int (Int.ofNat n))
          | .intSized .Signed sz, .uint n _ => some (.int (wrapSignedInt sz (Int.ofNat n)))
          | .intSized .Unsigned sz, .uint n _ => some (.uint (n % uintModulus sz) sz)
          | .int, .null => some (.int 0)
          | .int, .ptr _ offset => some (.int offset)
          | .intSized .Signed sz, .null => some (.int (wrapSignedInt sz 0))
          | .intSized .Unsigned sz, .null => some (.uint 0 sz)
          | .intSized .Signed sz, .ptr _ offset => some (.int (wrapSignedInt sz offset))
          | .intSized .Unsigned sz, .ptr _ offset =>
              some (.uint (wrapUnsignedNat sz offset) sz)
          | .ptr _, .int n =>
              if _h : 0 ≤ n then some (.ptr 0 n) else none
          | .ptr _, .uint n _ => some (.ptr 0 (Int.ofNat n))
          | .ptr _, .ptr block offset => some (.ptr block offset)
          | .ptr _, .null => some .null
          | .struct _, .ptr block offset => some (.ptr block offset)
          | .struct _, .null => some .null
          | .union _, .ptr block offset => some (.ptr block offset)
          | .union _, .null => some .null
          | .enum _, .int n => some (.int n)
          | .enum _, .uint n _ => some (.int (Int.ofNat n))
          | .enum _, .null => some (.int 0)
          | .typedef _, v => some v
          | .array _ _, .ptr block offset => some (.ptr block offset)
          | .array _ _, .null => some .null
          | .funcPtr _ _, .ptr block offset => some (.ptr block offset)
          | .funcPtr _ _, .null => some .null
          -- Float casts (operational, not IEEE-certified).
          | .float, .int n => some (.float (Float.ofInt n))
          | .float, .uint n _ => some (.float (Float.ofNat n))
          | .float, .float v => some (.float v)
          | .double, .int n => some (.float (Float.ofInt n))
          | .double, .uint n _ => some (.float (Float.ofNat n))
          | .double, .float v => some (.float v)
          | .int, .float v => some (.int (Int.ofNat v.toUInt64.toNat))
          | .intSized .Signed sz, .float v =>
              some (.int (wrapSignedInt sz (Int.ofNat v.toUInt64.toNat)))
          | .intSized .Unsigned sz, .float v =>
              some (.uint (v.toUInt64.toNat % uintModulus sz) sz)
          | .void, _ => some CVal.undef
          | _, .undef => some CVal.undef
          | _, _ => none
      | .binop .lAnd e1 e2 => do
          let v1 ← evalExpr e1 st
          if isTruthy v1 then
            let v2 ← evalExpr e2 st
            some (.int (if isTruthy v2 then 1 else 0))
          else
            some (.int 0)
      | .binop .lOr e1 e2 => do
          let v1 ← evalExpr e1 st
          if isTruthy v1 then
            some (.int 1)
          else
            let v2 ← evalExpr e2 st
            some (.int (if isTruthy v2 then 1 else 0))
      | .binop op e1 e2 => do
          let v1 ← evalExpr e1 st
          let v2 ← evalExpr e2 st
          evalBinOp op v1 v2
      | .deref e' => do
          let v ← evalExpr e' st
          match v with
          | .ptr block offset => st.readPtr { block := block, offset := offset }
          | _ => none
      | .addrOf x => do
          -- Simplified: look up variable; if it's a ptr, return it
          let _ ← st.lookupVar x
          none  -- addrOf for stack variables not modeled in this prototype
      | .arrayAccess arr idx => do
          let base ← evalExpr arr st
          let offset ← evalExpr idx st
          let ptr ← evalBinOp .add base offset
          match ptr with
          | .ptr block offset => st.readPtr { block := block, offset := offset }
          | _ => none
      | .fieldAccess e' field => do
          let v ← evalExpr e' st
          match v with
          | .ptr block offset => do
              let slot ← PtrVal.addOffset { block := block, offset := offset } (Int.ofNat (fieldOffset field))
              st.readPtr slot
          | _ => none
      | .call _ _ => none  -- function calls not modeled in big-step prototype
      | _ => none  -- intLit, null already handled by evalStaticExpr above

/-- Write `cells` consecutive heap cells starting at `addr`. -/
def writeBlock (h : Heap) (addr cells : Nat) (v : CVal := CVal.undef) : Heap :=
  (List.range cells).foldl (fun acc i => acc.write (addr + i) v) h

/-- Free `cells` consecutive heap cells starting at `addr`. -/
def freeBlock (h : Heap) (addr cells : Nat) : Heap :=
  (List.range cells).foldl (fun acc i => acc.free (addr + i)) h

namespace CState

/-- Allocate a fresh flat segment while also reserving a fresh `Mem` block. -/
def allocCells (st : CState) (x : String) (cells : Nat) : CState :=
  let addr := st.nextAddr
  let heap' := writeBlock st.heap addr cells
  let (block, mem') := st.mem.alloc 0 (Int.ofNat cells) .Freeable
  let alloc : FlatAlloc := { base := addr, block := block, cells := cells }
  { heap := heap'
    env := (x, .ptr block 0) :: st.env
    nextAddr := addr + cells
    mem := syncMem heap' (alloc :: st.allocs) mem'.nextBlock
    allocs := alloc :: st.allocs }

/-- Free a flat segment and drop the corresponding tracked `Mem` block when the
base address is known. -/
def freeCells (st : CState) (addr cells : Nat) : CState :=
  let heap' := freeBlock st.heap addr cells
  let allocs' := st.allocs.filter (fun alloc => alloc.base != addr)
  let nextHint :=
    match st.allocs.find? (fun alloc => alloc.base = addr) with
    | some alloc => max st.mem.nextBlock (alloc.block + 1)
    | none => st.mem.nextBlock
  { heap := heap'
    env := st.env
    nextAddr := st.nextAddr
    mem := syncMem heap' allocs' nextHint
    allocs := allocs' }

end CState

/-- Allocate a built-in struct block using its registered layout. -/
def allocStruct (layout : StructLayout) (st : CState) : CState × Nat :=
  let addr := st.nextAddr
  let st' := st.allocCells "_struct" layout.blockSize
  ({ st' with env := st.env }, addr)

/-- Free a built-in struct block using its registered layout. -/
def freeStruct (layout : StructLayout) (addr : Nat) (st : CState) : CState :=
  st.freeCells addr layout.blockSize

/-- Execution result. -/
inductive ExecResult where
  | normal : CState → ExecResult
  | returned : CVal → CState → ExecResult

/-- Big-step execution (fuel-bounded for while loops). -/
def execStmt : Nat → CStmt → CState → Option ExecResult
  | 0, _, _ => none  -- out of fuel
  | _, .skip, st => some (.normal st)
  | _, .ret e, st => do
      let v ← evalExpr e st
      some (.returned v st)
  | _, .alloc x cells, st =>
      some (.normal (st.allocCells x cells))
  | _, .free e cells, st => do
      let v ← evalExpr e st
      match v with
      | .ptr block offset =>
          let flatAddr ← st.resolvePtr { block := block, offset := offset }
          some (.normal (st.freeCells flatAddr cells))
      | _ => none
  | _, .decl x _, st =>
      some (.normal (st.updateVar x CVal.undef))
  | fuel + 1, .block decls body, st => do
      let entry := enterBlockState st decls
      match ← execStmt fuel body entry with
      | .normal st' => some (.normal (restoreBlockState st st' decls))
      | .returned v st' => some (.returned v (restoreBlockState st st' decls))
  | fuel + 1, .switch e tag caseBody default, st => do
      let v ← evalExpr e st
      match v with
      | .int n => if n = tag then execStmt fuel caseBody st else execStmt fuel default st
      | _ => none
  | fuel + 1, .forLoop init cond step body, st =>
      execStmt fuel (desugarFor init cond step body) st
  | _, .break, _ => none
  | _, .continue, _ => none
  | _ + 1, .assign lhs rhs, st => do
      let v ← evalExpr rhs st
      match lhs with
      | .var x => some (.normal (st.updateVar x v))
      | .deref p => do
          let pv ← evalExpr p st
          match pv with
          | .ptr block offset =>
              ExecResult.normal <$> st.writePtr { block := block, offset := offset } v
          | _ => none
      | .fieldAccess p field => do
          let pv ← evalExpr p st
          match pv with
          | .ptr block offset => do
              let slot ← PtrVal.addOffset { block := block, offset := offset } (Int.ofNat (fieldOffset field))
              ExecResult.normal <$> st.writePtr slot v
          | _ => none
      | _ => none
  | fuel + 1, .seq s1 s2, st => do
      match ← execStmt fuel s1 st with
      | .normal st' => execStmt fuel s2 st'
      | .returned v st' => some (.returned v st')
  | fuel + 1, .ite cond th el, st => do
      let v ← evalExpr cond st
      if isTruthy v then execStmt fuel th st
      else execStmt fuel el st
  | fuel + 1, .whileInv cond inv body, st => do
      let v ← evalExpr cond st
      if isTruthy v then
        match ← execStmt fuel body st with
        -- Execution ignores the invariant semantically, but we preserve it so
        -- future tooling sees the same loop annotation across iterations.
        | .normal st' => execStmt fuel (.whileInv cond inv body) st'
        | .returned v' st' => some (.returned v' st')
      else some (.normal st)

theorem execStmt_switch_eq_select (fuel : Nat) (e : CExpr)
    (tag : Int) (caseBody default : CStmt) (st : CState) :
    execStmt fuel (.switch e tag caseBody default) st =
      match fuel with
      | 0 => none
      | fuel' + 1 =>
          match evalExpr e st with
          | some (.int n) => if n = tag then execStmt fuel' caseBody st else execStmt fuel' default st
          | _ => none := by
  cases fuel with
  | zero =>
      simp [execStmt]
  | succ fuel' =>
      cases hEval : evalExpr e st with
      | none =>
          simp [execStmt, hEval]
      | some v =>
          cases v with
          | int n =>
              simp [execStmt, hEval]
          | ptr block offset =>
              simp [execStmt, hEval]
          | uint n sz =>
              simp [execStmt, hEval]
          | float v =>
              simp [execStmt, hEval]
          | null =>
              simp [execStmt, hEval]
          | undef =>
              simp [execStmt, hEval]
          | structVal fields =>
              simp [execStmt, hEval]
          | unionVal tag v =>
              simp [execStmt, hEval]

theorem execStmt_for_desugar (fuel : Nat) (init : CStmt) (cond : CExpr)
    (step body : CStmt) (st : CState) :
    execStmt (fuel + 1) (.forLoop init cond step body) st =
      execStmt fuel (desugarFor init cond step body) st := by
  simp [execStmt]

theorem execStmt_seq_of_normal
    (fuel : Nat) (s1 s2 : CStmt) (st st' : CState)
    (h : execStmt fuel s1 st = some (.normal st')) :
    execStmt (fuel + 1) (.seq s1 s2) st = execStmt fuel s2 st' := by
  simp [execStmt, h]

theorem execStmt_ite_of_eval_true
    (fuel : Nat) (cond : CExpr) (th el : CStmt) (st : CState) (v : CVal)
    (hEval : evalExpr cond st = some v) (hTruth : isTruthy v = true) :
    execStmt (fuel + 1) (.ite cond th el) st = execStmt fuel th st := by
  simp [execStmt, hEval, hTruth]

theorem execStmt_ite_of_eval_false
    (fuel : Nat) (cond : CExpr) (th el : CStmt) (st : CState) (v : CVal)
    (hEval : evalExpr cond st = some v) (hTruth : isTruthy v = false) :
    execStmt (fuel + 1) (.ite cond th el) st = execStmt fuel el st := by
  simp [execStmt, hEval, hTruth]

theorem execStmt_whileInv_of_eval_false
    (fuel : Nat) (cond : CExpr) (inv : HProp) (body : CStmt) (st : CState) (v : CVal)
    (hEval : evalExpr cond st = some v) (hTruth : isTruthy v = false) :
    execStmt (fuel + 1) (.whileInv cond inv body) st = some (.normal st) := by
  simp [execStmt, hEval, hTruth]

theorem execStmt_whileInv_of_eval_true_normal
    (fuel : Nat) (cond : CExpr) (inv : HProp) (body : CStmt) (st st' : CState) (v : CVal)
    (hEval : evalExpr cond st = some v) (hTruth : isTruthy v = true)
    (hBody : execStmt fuel body st = some (.normal st')) :
    execStmt (fuel + 1) (.whileInv cond inv body) st =
      execStmt fuel (.whileInv cond inv body) st' := by
  simp [execStmt, hEval, hTruth, hBody]

theorem execStmt_fuel_mono_step :
    ∀ {fuel : Nat} {stmt : CStmt} {st : CState} {res : ExecResult},
      execStmt fuel stmt st = some res →
        execStmt (fuel + 1) stmt st = some res
  | 0, _, _, _, h => by
      simp [execStmt] at h
  | fuel + 1, .skip, _, _, h => by
      simpa [execStmt] using h
  | fuel + 1, .ret e, _, _, h => by
      simpa [execStmt] using h
  | fuel + 1, .alloc x cells, _, _, h => by
      simpa [execStmt] using h
  | fuel + 1, .free e cells, _, _, h => by
      simpa [execStmt] using h
  | fuel + 1, .decl x ty, _, _, h => by
      simpa [execStmt] using h
  | fuel + 1, .break, _, _, h => by
      simp [execStmt] at h
  | fuel + 1, .continue, _, _, h => by
      simp [execStmt] at h
  | fuel + 1, .assign lhs rhs, _, _, h => by
      simpa [execStmt] using h
  | fuel + 1, .block decls body, st, res, h => by
      cases hbody : execStmt fuel body (enterBlockState st decls) <;> simp [execStmt, hbody] at h
      case some inner =>
        cases inner with
        | normal st' =>
            have hbody' :
                execStmt (fuel + 1) body (enterBlockState st decls) = some (.normal st') :=
              execStmt_fuel_mono_step (stmt := body) (st := enterBlockState st decls)
                (res := .normal st') hbody
            simpa [execStmt, hbody'] using h
        | returned v st' =>
            have hbody' :
                execStmt (fuel + 1) body (enterBlockState st decls) = some (.returned v st') :=
              execStmt_fuel_mono_step (stmt := body) (st := enterBlockState st decls)
                (res := .returned v st') hbody
            simpa [execStmt, hbody'] using h
  | fuel + 1, .switch e tag caseBody default, st, res, h => by
      cases hEval : evalExpr e st <;> simp [execStmt, hEval] at h
      case some v =>
        cases v <;> simp [execStmt, hEval] at h
        case int n =>
          by_cases htag : n = tag
          · have hcase : execStmt fuel caseBody st = some res := by
              simpa [execStmt, hEval, htag] using h
            have hcase' :
                execStmt (fuel + 1) caseBody st = some res :=
              execStmt_fuel_mono_step (stmt := caseBody) (st := st) (res := res) hcase
            simpa [execStmt, hEval, htag, hcase']
          · have hdefault : execStmt fuel default st = some res := by
              simpa [execStmt, hEval, htag] using h
            have hdefault' :
                execStmt (fuel + 1) default st = some res :=
              execStmt_fuel_mono_step (stmt := default) (st := st) (res := res) hdefault
            simpa [execStmt, hEval, htag, hdefault']
  | fuel + 1, .forLoop init cond step body, st, res, h => by
      have hdesugar :
          execStmt fuel (desugarFor init cond step body) st = some res := by
        simpa [execStmt] using h
      have hdesugar' :
          execStmt (fuel + 1) (desugarFor init cond step body) st = some res :=
        execStmt_fuel_mono_step (stmt := desugarFor init cond step body) (st := st) (res := res) hdesugar
      simpa [execStmt] using hdesugar'
  | fuel + 1, .seq s1 s2, st, res, h => by
      cases h1 : execStmt fuel s1 st <;> simp [execStmt, h1] at h
      case some r1 =>
        cases r1 with
        | normal st' =>
            have h1' :
                execStmt (fuel + 1) s1 st = some (.normal st') :=
              execStmt_fuel_mono_step (stmt := s1) (st := st) (res := .normal st') h1
            have h2' :
                execStmt (fuel + 1) s2 st' = some res :=
              execStmt_fuel_mono_step (stmt := s2) (st := st') (res := res) h
            simpa [execStmt, h1', h2']
        | returned v st' =>
            have h1' :
                execStmt (fuel + 1) s1 st = some (.returned v st') :=
              execStmt_fuel_mono_step (stmt := s1) (st := st) (res := .returned v st') h1
            simpa [execStmt, h1'] using h
  | fuel + 1, .ite cond th el, st, res, h => by
      cases hEval : evalExpr cond st <;> simp [execStmt, hEval] at h
      case some v =>
        cases hTruth : isTruthy v <;> simp [execStmt, hEval, hTruth] at h
        case false =>
            have hel' :
                execStmt (fuel + 1) el st = some res :=
              execStmt_fuel_mono_step (stmt := el) (st := st) (res := res) h
            simpa [execStmt, hEval, hTruth, hel']
        case true =>
            have hth' :
                execStmt (fuel + 1) th st = some res :=
              execStmt_fuel_mono_step (stmt := th) (st := st) (res := res) h
            simpa [execStmt, hEval, hTruth, hth']
  | fuel + 1, .whileInv cond inv body, st, res, h => by
      cases hEval : evalExpr cond st <;> simp [execStmt, hEval] at h
      case some v =>
        cases hTruth : isTruthy v <;> simp [execStmt, hEval, hTruth] at h
        case false =>
          simpa [execStmt, hEval, hTruth] using h
        case true =>
          cases hBody : execStmt fuel body st <;> simp [execStmt, hEval, hTruth, hBody] at h
          case some bodyRes =>
            cases bodyRes with
            | normal st' =>
                have hBody' :
                    execStmt (fuel + 1) body st = some (.normal st') :=
                  execStmt_fuel_mono_step (stmt := body) (st := st) (res := .normal st') hBody
                have hLoop' :
                    execStmt (fuel + 1) (.whileInv cond inv body) st' = some res :=
                  execStmt_fuel_mono_step (stmt := .whileInv cond inv body) (st := st')
                    (res := res) h
                simpa [execStmt, hEval, hTruth, hBody', hLoop']
            | returned v' st' =>
                have hBody' :
                    execStmt (fuel + 1) body st = some (.returned v' st') :=
                  execStmt_fuel_mono_step (stmt := body) (st := st) (res := .returned v' st') hBody
                simpa [execStmt, hEval, hTruth, hBody'] using h

theorem execStmt_fuel_mono
    {fuel extra : Nat} {stmt : CStmt} {st : CState} {res : ExecResult}
    (h : execStmt fuel stmt st = some res) :
    execStmt (fuel + extra) stmt st = some res := by
  induction extra generalizing fuel stmt st res with
  | zero =>
      simpa using h
  | succ extra ih =>
      have h' : execStmt (fuel + extra) stmt st = some res := ih h
      have h'' :
          execStmt ((fuel + extra) + 1) stmt st = some res :=
        execStmt_fuel_mono_step (stmt := stmt) (st := st) (res := res) h'
      simpa [Nat.add_assoc] using h''

/-- Run a C function spec on concrete arguments. -/
def runSpec (spec : CFunSpec) (args : List CVal) (fuel : Nat := 10000) :
    Option CVal := do
  let env := spec.params.zip args |>.map fun ((name, _), val) => (name, val)
  let st : CState := { heap := Heap.empty, env := env, nextAddr := 100 }
  match ← execStmt fuel spec.body st with
  | .returned v _ => some v
  | .normal _ => none

theorem execStmt_whileInv_inv_irrelevant
    (fuel : Nat) (cond : CExpr) (body : CStmt) (inv1 inv2 : HProp) (st : CState) :
    execStmt fuel (.whileInv cond inv1 body) st =
      execStmt fuel (.whileInv cond inv2 body) st := by
  induction fuel generalizing st with
  | zero =>
      simp [execStmt]
  | succ fuel ih =>
      cases hcond : evalExpr cond st with
      | none =>
          simp [execStmt, hcond]
      | some v =>
          cases htruth : isTruthy v with
          | false =>
              simp [execStmt, hcond, htruth]
          | true =>
              cases hbody : execStmt fuel body st with
              | none =>
                  simp [execStmt, hcond, htruth, hbody]
              | some res =>
                  cases res with
                  | normal st' =>
                      simp [execStmt, hcond, htruth, hbody]
                      exact ih st'
                  | returned v' st' =>
                      simp [execStmt, hcond, htruth, hbody]

end HeytingLean.LeanCP
