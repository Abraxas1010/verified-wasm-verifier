import HeytingLean.Rel.Basic

/-!
# VETT.Rel.Basic

Re-export of `HeytingLean.Rel.Basic` into the `HeytingLean.VETT.Rel` namespace.

Phase 10’s strict VETT model uses `Prop`-valued relations as the canonical concrete model for
VETT’s “set connectives”, where the strict restriction commutation laws hold definitionally.
-/

namespace HeytingLean.VETT.Rel

abbrev HRel := HeytingLean.Rel.HRel

namespace RelOps

export HeytingLean.Rel.RelOps
  ( restrict
    restrict_apply
    restrict_id
    restrict_comp
    unit
    unit_apply
    homProarrow
    tensor
    top
    prod
    covHom
    contraHom
    tensor_restrict_strict
    covHom_restrict_strict
    contraHom_restrict_strict
    top_restrict_strict
    prod_restrict_strict
    unit_restrict_strict
  )

end RelOps

end HeytingLean.VETT.Rel
