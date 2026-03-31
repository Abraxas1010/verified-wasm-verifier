import HeytingLean.LoF.ICC.Syntax
import HeytingLean.LoF.ICCKernel.Syntax

/-!
# ICCKernel.Term → ICC.Term Projection

Project the 14-constructor kernel term down to the 5-constructor
verified ICC core. This is the first gap in the pipeline:

```
Lean.Expr ──lowerExprCore──→ ICCKernel.Term ──projectToICC──→ ICC.Term
              (EXISTS)            (14 ctors)     (THIS FILE)     (5 ctors)
```

## Constructor handling

| ICCKernel constructor | ICC.Term mapping |
|---|---|
| `bvar idx` | `var idx` |
| `app fn arg` | `app fn arg` |
| `lam _ _ _ body` | `lam body` (strip binder info + type) |
| `bridge body` | `bridge body` |
| `ann val typ` | `ann val typ` |
| `forallE _ _ _ body` | `bridge body` (Pi type → bridge) |
| `letE _ _ val body _` | `app (lam body) val` (let = beta redex) |
| `const _ _` | `var 0` (opaque reference; Phase 2 adds delta-expansion) |
| `sort _` | `var 0` (universe erased) |
| `fvar _` | `var 0` (should not appear in kernel terms) |
| `mvar _` | `var 0` (should not appear in elaborated terms) |
| `lit _` | `var 0` (literal erased) |
| `mdata _ body` | recurse on body (strip metadata) |
| `proj _ _ body` | `app (var 0) body` (projection → application) |
-/

namespace LeanClef.Bridge

/-- Abbreviation for the 14-constructor kernel term type. -/
abbrev KTerm := HeytingLean.LoF.ICCKernel.Term

/-- Abbreviation for the 5-constructor verified ICC term type. -/
abbrev ITerm := HeytingLean.LoF.ICC.Term

/-- Project a 14-constructor ICCKernel.Term to the 5-constructor ICC.Term.

    The projection is total: every kernel constructor maps to a valid ICC term.
    Constructors outside the verified core are mapped to canonical representatives
    (var 0 for opaque references, bridge for Pi types, app+lam for let-bindings). -/
def projectToICC : KTerm → ITerm
  | .bvar idx        => .var idx
  | .fvar _          => .var 0
  | .mvar _          => .var 0
  | .sort _          => .var 0
  | .const _ _       => .var 0
  | .app fn arg      => .app (projectToICC fn) (projectToICC arg)
  | .lam _ _ _ body  => .lam (projectToICC body)
  | .forallE _ _ _ body => .bridge (projectToICC body)
  | .letE _ _ val body _ => .app (.lam (projectToICC body)) (projectToICC val)
  | .lit _           => .var 0
  | .mdata _ body    => projectToICC body
  | .proj _ _ body   => .app (.var 0) (projectToICC body)
  | .bridge body     => .bridge (projectToICC body)
  | .ann val typ     => .ann (projectToICC val) (projectToICC typ)

/-- Beta redexes in kernel terms map to beta redexes in ICC terms. -/
theorem projectToICC_preserves_app_lam
    (n : HeytingLean.LoF.ICCKernel.Name)
    (bi : HeytingLean.LoF.ICCKernel.BinderStyle)
    (ty body arg : KTerm) :
    projectToICC (.app (.lam n bi ty body) arg) =
    HeytingLean.LoF.ICC.Term.app
      (HeytingLean.LoF.ICC.Term.lam (projectToICC body))
      (projectToICC arg) := by
  simp [projectToICC]

/-- Let-bindings project to beta redexes. -/
theorem projectToICC_letE_is_beta
    (n : HeytingLean.LoF.ICCKernel.Name)
    (ty val body : KTerm) (nd : Bool) :
    projectToICC (.letE n ty val body nd) =
    HeytingLean.LoF.ICC.Term.app
      (HeytingLean.LoF.ICC.Term.lam (projectToICC body))
      (projectToICC val) := by
  simp [projectToICC]

/-- Metadata stripping is transparent to projection. -/
theorem projectToICC_mdata_strip
    (entries : List HeytingLean.LoF.ICCKernel.MetadataEntry)
    (body : KTerm) :
    projectToICC (.mdata entries body) = projectToICC body := by
  simp [projectToICC]

end LeanClef.Bridge
