import HeytingLean.Core.Nucleus

/-!
# IteratedVirtual.Bridge.HeytingConnection

Strict-only “stability transport” lemmas for nuclei.

The IteratedVirtual layer (virtual equipments, cobordism chains, helix energy) frequently wants a
generic statement of the form:

> if `x` is *stable* (a nucleus fixed point), then its image under a structure-preserving map is
> also stable.

This file provides that statement **honestly** under explicit hypotheses: a map that commutes with
the nucleus action.

We do **not** assume that a `VirtualEquipment` “induces” a nucleus by default, because the current
`IteratedVirtual.VirtualEquipment` is data-only and has no closure operator field.
-/

namespace HeytingLean
namespace IteratedVirtual
namespace Bridge

open HeytingLean.Core

universe u v

section
  variable {α : Type u} {β : Type v}
  variable [SemilatticeInf α] [OrderBot α]
  variable [SemilatticeInf β] [OrderBot β]

  /-- A map between nucleus-equipped semilattices that commutes with the nucleus action. -/
  structure NucleusHom (Nα : Nucleus α) (Nβ : Nucleus β) where
    toFun : α → β
    map_bot : toFun ⊥ = ⊥
    map_inf : ∀ a b, toFun (a ⊓ b) = toFun a ⊓ toFun b
    comm : ∀ a, toFun (Nα.R a) = Nβ.R (toFun a)

  instance {Nα : Nucleus α} {Nβ : Nucleus β} : CoeFun (NucleusHom (α := α) (β := β) Nα Nβ) (fun _ => α → β) where
    coe f := f.toFun

  /-- If `a` is fixed by `Nα`, then `f a` is fixed by `Nβ` provided `f` commutes with the nuclei. -/
  theorem fixedPoint_map {Nα : Nucleus α} {Nβ : Nucleus β} (f : NucleusHom (α := α) (β := β) Nα Nβ)
      {a : α} (ha : Nα.R a = a) :
      Nβ.R (f a) = f a := by
    -- `f (Nα.R a) = f a` and `f (Nα.R a) = Nβ.R (f a)`
    have : f (Nα.R a) = f a := by simp [ha]
    -- rewrite via commutation
    simpa [f.comm] using this

end

end Bridge
end IteratedVirtual
end HeytingLean
