import HeytingLean.Constructor.Core
import HeytingLean.Numbers.Surreal.ClosureReentry

/-!
# Surreal substrate adapter for Constructor meta-theory

A first, intentionally small adapter that instantiates the abstract
`Constructor.Meta` interface for the Surreal closure nucleus on
`Set PreGame`.

This gives a concrete but minimal `Meta` instance:
* carrier `α := Set SurrealCore.PreGame`,
* nucleus `R := Surreal.closureCore`,
* a network syntax (`Network`) with a basic denotation,
* Occam / PSR / Dialectic wired to simple set-based instantiations.

The goal is to provide a numbers-first substrate that type-checks and can
later be refined without touching the core interface.
-/

open Classical
open Set

namespace HeytingLean
namespace Constructor
namespace SurrealAdapter

open Numbers
open Numbers.Surreal
open Numbers.SurrealCore

/-- `PreGame` is trivially inhabited by the empty game. -/
instance : Nonempty PreGame :=
  ⟨{ L := [], R := [], birth := 0 }⟩

/-- Ambient carrier for the Surreal Constructor substrate:
sets of pre-games. -/
abbrev Carrier : Type := Set SurrealCore.PreGame

/-- Surreal closure nucleus on `Set PreGame` (Option A). -/
abbrev Rcl : Nucleus Carrier :=
  closureCore

noncomputable instance : CompleteLattice Carrier :=
  inferInstance

/-- Network syntax for the Surreal adapter: finite wiring trees built from
atomic carrier elements, with sequential (`seq`) and parallel (`par`)
composition nodes. This is a first, lightweight notion of networks that
can be refined later without changing the core `Meta` interface. -/
inductive Network where
  | atom (a : Carrier)
  | seq (N₁ N₂ : Network)
  | par (N₁ N₂ : Network)

/-- Collect the carrier components that appear in a network. -/
def networkComponents : Network → Multiset Carrier
  | Network.atom a    => {a}
  | Network.seq N₁ N₂ => networkComponents N₁ + networkComponents N₂
  | Network.par N₁ N₂ => networkComponents N₁ + networkComponents N₂

/-- Well-formedness predicate for Surreal networks:
atoms must be globally possible for `Rcl`, and composite networks are
regular exactly when all of their sub-networks are regular. -/
def networkRegular : Network → Prop
  | Network.atom a    => possible Rcl a
  | Network.seq N₁ N₂ => networkRegular N₁ ∧ networkRegular N₂
  | Network.par N₁ N₂ => networkRegular N₁ ∧ networkRegular N₂

/-- Denotation of a network as a single carrier element:
* atoms denote their attached carrier set;
* sequential composition uses meet (`⊓`);
* parallel composition uses join (`⊔`). -/
def networkDenote : Network → Carrier
  | Network.atom a    => a
  | Network.seq N₁ N₂ => networkDenote N₁ ⊓ networkDenote N₂
  | Network.par N₁ N₂ => networkDenote N₁ ⊔ networkDenote N₂

/-- A canonical element of the Surreal closure core: the empty pre-game
with no left or right options, which is legal and fixed by `canonicalize`. -/
lemma build_mem_canonicalCore :
    SurrealCore.PreGame.build [] [] ∈ canonicalCore := by
  -- Unfold the definition of membership in `canonicalCore`.
  change
    SurrealCore.legal (SurrealCore.PreGame.build [] []) ∧
      SurrealCore.canonicalize (SurrealCore.PreGame.build [] []) =
        SurrealCore.PreGame.build [] []
  constructor
  · -- Legality is vacuous because the move lists are empty.
    intro l hl r hr
    cases hl
  · -- `canonicalize` is the identity.
    simp [SurrealCore.canonicalize]

/-- The canonical core element lies in the closure of every carrier set. -/
lemma build_in_closure (S : Carrier) :
    SurrealCore.PreGame.build [] [] ∈ Rcl S := by
  have hCore : SurrealCore.PreGame.build [] [] ∈ canonicalCore :=
    build_mem_canonicalCore
  -- Membership in the closure nucleus is membership in `S ∪ canonicalCore`.
  change SurrealCore.PreGame.build [] [] ∈ closureCore S
  have : SurrealCore.PreGame.build [] [] ∈ (S ∪ canonicalCore) :=
    Or.inr hCore
  simpa [closureCore, canonicalCore] using this

/-- Constructor meta-theory instance for the Surreal closure nucleus.

This instance uses the `Network` syntax above together with the denotation
`networkDenote`. The current proof of `composition_principle` is intentionally
minimal: it only relies on the fact that the closure core is never empty,
and does not yet use the component-wise hypotheses in a strong way. -/
noncomputable instance surrealMeta : Meta (α := Carrier) Rcl where
  Network := Network

  components := networkComponents

  denote := networkDenote

  regular := networkRegular

  composition_principle := by
    intro N _ _
    -- `possible Rcl (networkDenote N)` holds because the closure core always
    -- contains a canonical pre-game.
    have hMem : SurrealCore.PreGame.build [] [] ∈ Rcl (networkDenote N) :=
      build_in_closure (S := networkDenote N)
    -- Show that `Rcl (networkDenote N)` is nonempty using this witness.
    unfold possible
    intro hbot
    -- Under `hbot : Rcl (networkDenote N) = ⊥`, the witness `hMem` would
    -- have to lie in bottom, which is impossible.
    have hbotMem := hMem
    simp [hbot] at hbotMem

  -- Information variables are, for now, those sets that coincide with `⊤` and
  -- are globally possible for `Rcl`.
  isInfoVariable := fun (a : Carrier) => a = ⊤ ∧ possible Rcl a

  interoperability := by
    intro x y hx hy
    rcases hx with ⟨hx_eq, hx_pos⟩
    rcases hy with ⟨hy_eq, hy_pos⟩
    subst hx_eq
    subst hy_eq
    -- Now `x = ⊤` and `y = ⊤`.
    -- In any bounded lattice, `⊤ ⊓ a = a`.
    have hinf : (⊤ : Carrier) ⊓ ⊤ = (⊤ : Carrier) :=
      top_inf_eq (⊤ : Carrier)
    refine And.intro ?hinfo ?hposs
    · -- `isInfoVariable (⊤ ⊓ ⊤)` holds.
      refine And.intro ?heq ?hpos
      · exact hinf
      · -- `possible Rcl (⊤ ⊓ ⊤)` via a direct calculation.
        simp [possible, Rcl, closureCore, canonicalCore, univ_union]
    · -- `possible Rcl (⊤ ⊓ ⊤)` as above.
      simp [possible, Rcl, closureCore, canonicalCore, univ_union]

  -- Locality baseline: any `R`-stable meet `a ⊓ b` can be factored through its
  -- components by taking `a' = R a` and `b' = R b`. For the Surreal closure nucleus
  -- this gives a trivial but lawful factorisation.
  locality := by
    intro a b hfix
    refine ⟨Rcl a, Rcl b, rfl, rfl, ?_⟩
    -- `Rcl` is a nucleus, so it preserves infima.
    have hmap : Rcl (a ⊓ b) = Rcl a ⊓ Rcl b :=
      Nucleus.map_inf (n := Rcl) (x := a) (y := b)
    -- Combine with the stability hypothesis `Rcl (a ⊓ b) = a ⊓ b`.
    have h' : a ⊓ b = Rcl a ⊓ Rcl b := by
      calc
        a ⊓ b = Rcl (a ⊓ b) := hfix.symm
        _ = Rcl a ⊓ Rcl b := hmap
    exact h'.symm

  -- Occam operator: apply the closure nucleus, viewing the resulting element as
  -- the canonical stabilised explanation associated to a carrier element.
  Occam a := Rcl a

  -- PSR predicate: a carrier element satisfies PSR when it is a fixed point of
  -- the closure nucleus.
  PSR a := Rcl a = a

  -- Dialectic baseline: re-entry of the join of two configurations.
  Dialectic a b := Rcl (a ⊔ b)

end SurrealAdapter
end Constructor
end HeytingLean
