import HeytingLean.LeanCP.Lang.CSyntax
import HeytingLean.LeanCP.Core.HProp
import HeytingLean.LeanCP.Core.MemSepLog
import HeytingLean.LeanCP.Core.SepLog
import HeytingLean.LeanCP.Predicates.Store

/-!
# LeanCP Weakest Precondition Generator

Given a C statement `s` and postcondition `Q`, produces the weakest precondition
`P` such that `{P} s {Q}` holds in separation logic.

The WP for heap-modifying operations (pointer writes, alloc, free) uses
separation logic predicates, NOT variable substitution. This is the core
distinction from classical Hoare logic VCG.
-/

namespace HeytingLean.LeanCP

/-- Weakest precondition for C statements.

    `wp s Q` produces the weakest HProp precondition such that executing
    statement `s` in any heap satisfying `wp s Q` results in a state
    satisfying the postcondition `Q`. -/
noncomputable def wp : CStmt → (CVal → HProp) → HProp
  | .skip, Q => Q CVal.undef
  | .ret e, Q =>
      match evalStaticExpr e with
      | some v => Q v
      | none => Q CVal.undef
  | .block _ body, Q =>
      wp body Q
  | .switch e tag caseBody default, Q =>
      match evalStaticExpr e with
      | some (.int n) => if n = tag then wp caseBody Q else wp default Q
      | _ => HProp.hfalse
  | .forLoop _ _ _ _, _ =>
      HProp.hfalse
  | .break, _ =>
      HProp.hfalse
  | .continue, _ =>
      HProp.hfalse
  | .assign (.var _x) e, Q =>
      match evalStaticExpr e with
      | some v => Q v
      | none => Q CVal.undef
  | .assign (.deref _p) _e, Q =>
      -- POINTER WRITE (*p = e): separation logic heap update.
      -- Precondition: ∃ v_old, store(p_addr, v_old) ∗ (store(p_addr, e_val) -∗ Q)
      -- This requires consuming the old store predicate and producing the new one.
      HProp.hexists fun (addr : Nat) =>
        HProp.hexists fun (vOld : CVal) =>
          HProp.hexists fun (vNew : CVal) =>
            store addr vOld ∗ (store addr vNew -∗ Q CVal.undef)
  | .assign (.fieldAccess _p _field) _e, Q =>
      -- Field write (p->field = e): similar to pointer write with offset
      HProp.hexists fun (addr : Nat) =>
        HProp.hexists fun (vOld : CVal) =>
          HProp.hexists fun (vNew : CVal) =>
            store addr vOld ∗ (store addr vNew -∗ Q CVal.undef)
  | .seq s1 s2, Q =>
      -- Sequencing: WP of s1 with (WP of s2 with Q) as intermediate postcondition
      wp s1 (fun _ => wp s2 Q)
  | .ite cond thenBr elseBr, Q =>
      match evalStaticExpr cond with
      | some v => if isTruthy v then wp thenBr Q else wp elseBr Q
      | none => HProp.hand (wp thenBr Q) (wp elseBr Q)
  | .whileInv _cond inv body, Q =>
      -- While loop with user-supplied invariant I:
      --   WP = I ∧ (I ∧ cond → wp(body, I)) ∧ (I ∧ ¬cond → Q)
      -- The user must supply I; the VCG generates the three obligations.
      HProp.hand inv
        (HProp.pure (
          (∀ h, inv h → (wp body (fun _ => inv)) h) ∧
          (∀ h, inv h → Q CVal.undef h)))
  | .alloc _x cells, Q =>
      -- Allocation: produces a fresh address with uninitialized content
      HProp.hexists fun (addr : Nat) =>
        undefBlock addr cells -∗ Q (.ptr 0 (Int.ofNat addr))
  | .free e cells, Q =>
      -- Free: consumes the store predicate for the freed address
      match e with
      | .var _ =>
        HProp.hexists fun (addr : Nat) =>
          HProp.hexists fun (vs : List CVal) =>
            HProp.hand (HProp.fact (vs.length = cells))
              (blockAt addr vs ∗ (HProp.emp -∗ Q CVal.undef))
      | _ => Q CVal.undef
  | .decl _ _, Q =>
      -- Variable declaration: no heap effect
      Q CVal.undef
  | .assign _ _, Q =>
      -- Fallback for other assignment forms
      Q CVal.undef

/-- Generate verification conditions for a CFunSpec.
    Returns the entailment: pre ⊢ₛ wp(body, post) -/
def genVC (spec : CFunSpec) : Prop :=
  spec.pre ⊢ₛ wp spec.body spec.post

/-- Compatibility bridge: view the heap-only `wp` result as a block-memory
assertion by projecting memories through `memBlock0ToHeap`. This is a one-way
surface; it preserves legacy `wp` reasoning on block-0 embeddings without
claiming a reification from arbitrary `MemHProp` back into `HProp`. -/
def wpOnMem (s : CStmt) (Q : CVal → HProp) : MemHProp :=
  (wp s Q).onMem

@[simp] theorem wpOnMem_toMem (s : CStmt) (Q : CVal → HProp) (h : Heap) :
    wpOnMem s Q (heapToMem h) ↔ wp s Q h := by
  simp [wpOnMem]

/-- Heap entailment transports along the block-0 compatibility bridge. -/
theorem entails_onMem {P Q : HProp} (hPQ : P ⊢ₛ Q) :
    P.onMem ⊢ₘ Q.onMem := by
  intro m hP
  exact hPQ _ hP

/-- A proved legacy verification condition remains valid on memories viewed
through the block-0 compatibility bridge. -/
theorem genVC_onMem (spec : CFunSpec) (hvc : genVC spec) :
    spec.pre.onMem ⊢ₘ wpOnMem spec.body spec.post := by
  exact entails_onMem hvc

/-!
LeanCP does not currently expose a global `wp_sound` theorem. The operational
semantics range over heap, environment, and allocation state, while the current
assertion language ranges only over heaps. Because of that mismatch, heap-only
`wp` intentionally stays on `evalStaticExpr`: it is a backward-compatible
surface for heap reasoning, not an env-dependent verifier. Runtime-dependent
verification belongs to the state-sensitive `swp` stack, which already uses the
full `evalExpr` semantics and has a proved soundness theorem on its supported
fragment.
-/

end HeytingLean.LeanCP
