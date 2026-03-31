import HeytingLean.LeanCP.VCG.WP
import HeytingLean.LeanCP.VCG.SMT
import HeytingLean.LeanCP.Tactics.XSimp
import Auto

/-!
# LeanCP Main Solver Tactic

`leancp_solve` is the primary user-facing tactic. It:
1. Applies WP rules to reduce annotated C to Lean goals
2. Applies `leancp_xsimp` to simplify heap entailments
3. Dispatches remaining goals to `auto` (lean-auto) for SMT solving
4. If SMT fails, leaves goals for interactive proof

## SMT Integration

Uses `lean-auto`'s `auto` tactic with explicit fail-closed SMT configuration.
LeanCP never enables `auto.smt.trust`; solver success must still elaborate in
Lean, or the goal remains open for interactive proof.
-/

namespace HeytingLean.LeanCP

/-- `leancp_wp` — unfold the WP definition to expose proof obligations. -/
syntax "leancp_wp" : tactic
macro_rules
  | `(tactic| leancp_wp) => `(tactic|
      simp only [genVC, wp, entails, HProp.sep, HProp.emp, HProp.pure,
                  evalStaticExpr, evalBinOp, isTruthy,
                  HProp.hexists, HProp.hand, HProp.wand, HProp.pointsTo,
                  store, Heap.empty, Heap.write, Heap.union])

/-- `leancp_solve` — the main LeanCP tactic pipeline.
    Attempts: WP unfolding → xsimp → lean-auto → interactive fallback -/
syntax "leancp_solve" : tactic
syntax "leancp_smt_z3" : tactic
syntax "leancp_smt_cvc5" : tactic
syntax "leancp_vc_solve" : tactic
syntax "leancp_vc_solve_cvc5" : tactic

macro_rules
  | `(tactic| leancp_smt_z3) => `(tactic|
      (set_option auto.smt true in
       set_option auto.tptp false in
       set_option auto.smt.trust false in
       set_option auto.smt.solver.name "z3" in
       auto))

macro_rules
  | `(tactic| leancp_smt_cvc5) => `(tactic|
      (set_option auto.smt true in
       set_option auto.tptp false in
       set_option auto.smt.trust false in
       set_option auto.smt.solver.name "cvc5" in
       auto))

macro_rules
  | `(tactic| leancp_vc_solve) => `(tactic|
      (try intros)
      <;> try simp_all
      <;> try omega
      <;> try leancp_xsimp
      <;> first
        | leancp_smt_z3
        | leancp_smt_cvc5
        | auto
        | assumption)

macro_rules
  | `(tactic| leancp_vc_solve_cvc5) => `(tactic|
      (try intros)
      <;> try simp_all
      <;> try omega
      <;> try leancp_xsimp
      <;> first
        | leancp_smt_cvc5
        | leancp_smt_z3
        | auto
        | assumption)

macro_rules
  | `(tactic| leancp_solve) => `(tactic|
      (leancp_wp
       <;> leancp_vc_solve))

end HeytingLean.LeanCP
