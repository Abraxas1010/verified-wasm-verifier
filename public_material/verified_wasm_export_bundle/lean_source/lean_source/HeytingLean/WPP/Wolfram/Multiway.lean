import Mathlib.Data.Finset.Pi
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import HeytingLean.WPP.Multiway
import HeytingLean.WPP.Wolfram.Rewrite

namespace HeytingLean
namespace WPP
namespace Wolfram

/-!
# Wolfram multiway semantics (finite enumerator + ordering functions)

This module complements the terminating-independence development by providing:

1. A **finite** multiway-step enumerator for SetReplace-style systems, suitable for
   `Finset`-based exploration and for instantiating the generic WPP interface
   `HeytingLean.WPP.WppRule`.
2. A notion of **ordering function** (scheduler/strategy) producing deterministic
   singleway traces.

The enumerator is intentionally scoped to finite vertex/pattern types so that we can
compute a `Finset` of possible next states.
-/

universe u v

namespace System

variable {V : Type u} {P : Type v} (sys : System V P)

section Finite

variable [Fintype P] [DecidableEq P] [Fintype V] [DecidableEq V]

/-- Pure event *data* for finite enumeration: a rule index together with a substitution. -/
abbrev EventData : Type (max u v) := Fin sys.rules.length × (P → V)

namespace EventData

variable {sys}

/-- Applicability of event data to a state: the instantiated LHS is a submultiset. -/
def Applicable (ed : sys.EventData) (s : HGraph V) : Prop :=
  (sys.rules.get ed.1).instLhs ed.2 ≤ s

instance (ed : sys.EventData) (s : HGraph V) : Decidable (ed.Applicable (sys := sys) s) := by
  dsimp [Applicable]
  infer_instance

/-- Apply event data to a state (replacement of instantiated LHS by RHS). -/
def apply (ed : sys.EventData) (s : HGraph V) : HGraph V :=
  s - (sys.rules.get ed.1).instLhs ed.2 + (sys.rules.get ed.1).instRhs ed.2

end EventData

/-- All substitutions `P → V` (finite enumerator). -/
def allSubsts : Finset (P → V) :=
  ((Finset.univ : Finset P).pi (fun _ : P => (Finset.univ : Finset V))).image (fun f a =>
    f a (by simp))

/-- `allSubsts` really enumerates *all* functions `P → V`. -/
lemma mem_allSubsts (σ : P → V) : σ ∈ allSubsts (P := P) (V := V) := by
  let f : ∀ a, a ∈ (Finset.univ : Finset P) → V := fun a _ => σ a
  have hf : f ∈ (Finset.univ : Finset P).pi (fun _ : P => (Finset.univ : Finset V)) := by
    -- Membership in `pi` is pointwise membership in `Finset.univ`.
    simp [f]
  refine Finset.mem_image.mpr ?_
  refine ⟨f, hf, ?_⟩
  funext a
  simp [f]

/-- All injective substitutions `P → V` (finite enumerator). -/
def allInjSubsts : Finset (P → V) :=
  (allSubsts (P := P) (V := V)).filter Function.Injective

lemma mem_allInjSubsts_iff (σ : P → V) :
    σ ∈ allInjSubsts (P := P) (V := V) ↔ Function.Injective σ := by
  have hmem : σ ∈ allSubsts (P := P) (V := V) := mem_allSubsts (P := P) (V := V) σ
  simp [System.allInjSubsts, hmem]

/-- All event-data pairs (rule index × substitution). -/
def allEventData (sys : System V P) : Finset sys.EventData :=
  (Finset.univ.product (allSubsts (P := P) (V := V)))

lemma mem_allEventData_iff {ed : sys.EventData} :
    ed ∈ sys.allEventData ↔ ed.2 ∈ allSubsts (P := P) (V := V) := by
  simp [System.allEventData]

/-- Outgoing edges from a state in the multiway graph (event-data labeled). -/
def stepEdges (s : HGraph V) : Finset (sys.EventData × HGraph V) :=
  ((sys.allEventData.filter (fun ed => EventData.Applicable (sys := sys) ed s))).image (fun ed =>
    (ed, EventData.apply (sys := sys) ed s))

lemma mem_stepEdges_iff {s t : HGraph V} {ed : sys.EventData} :
    (ed, t) ∈ sys.stepEdges s ↔
      ed ∈ sys.allEventData ∧
      EventData.Applicable (sys := sys) ed s ∧
      EventData.apply (sys := sys) ed s = t := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨ed', hed', hEq⟩
    rcases Finset.mem_filter.mp hed' with ⟨hed'All, hed'App⟩
    have hedEq : ed' = ed := congrArg Prod.fst hEq
    have hedAll : ed ∈ sys.allEventData := by
      simpa [hedEq] using hed'All
    have hedApp : EventData.Applicable (sys := sys) ed s := by
      simpa [hedEq] using hed'App
    have htEq : EventData.apply (sys := sys) ed s = t := by
      have htEq' : EventData.apply (sys := sys) ed' s = t := by
        simpa using congrArg Prod.snd hEq
      simpa [hedEq] using htEq'
    exact ⟨hedAll, hedApp, htEq⟩
  · rintro ⟨hedAll, hedApp, htEq⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨ed, Finset.mem_filter.mpr ⟨hedAll, hedApp⟩, ?_⟩
    simp [htEq]

/-- The set of next states from `s` (duplicates removed). -/
def stepStates (s : HGraph V) : Finset (HGraph V) :=
  (sys.stepEdges s).image Prod.snd

lemma mem_stepStates_iff {s t : HGraph V} :
    t ∈ sys.stepStates s ↔
      ∃ ed, ed ∈ sys.allEventData ∧
        EventData.Applicable (sys := sys) ed s ∧
        EventData.apply (sys := sys) ed s = t := by
  constructor
  · intro ht
    rcases Finset.mem_image.mp ht with ⟨p, hp, hp2⟩
    rcases sys.mem_stepEdges_iff.mp hp with ⟨hedAll, hedApp, happly⟩
    refine ⟨p.1, hedAll, hedApp, ?_⟩
    exact happly.trans hp2
  · rintro ⟨ed, hedAll, hedApp, htEq⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨(ed, EventData.apply (sys := sys) ed s), ?_, ?_⟩
    · exact (sys.mem_stepEdges_iff).2 ⟨hedAll, hedApp, rfl⟩
    · simp [htEq]

/-- Instantiate the generic WPP multiway interface on finite Wolfram systems. -/
def toWppRule : WppRule (HGraph V) :=
  { step := fun s => sys.stepStates s }

/-- States reachable in exactly `n` multiway steps (finite approximation). -/
def statesAtDepth : Nat → Finset (HGraph V)
  | 0 => {sys.init}
  | n + 1 => (statesAtDepth n).biUnion (fun s => sys.stepStates s)

end Finite

/-! ## Ordering functions (deterministic schedulers) -/

section Ordering

variable [DecidableEq V]

/-- An ordering function chooses at most one next event, and must choose only applicable events. -/
structure Ordering where
  choose : HGraph V → Option sys.Event
  sound : ∀ {s e}, choose s = some e → e.Applicable (sys := sys) s

namespace Ordering

variable {sys}

/-- Deterministic evolution under an ordering function. -/
inductive EvolvesBy (ord : Ordering (sys := sys)) : HGraph V → List sys.Event → HGraph V → Prop
| nil (s : HGraph V) : EvolvesBy ord s [] s
| cons {s : HGraph V} {es : List sys.Event} {t : HGraph V} (e : sys.Event) :
    ord.choose s = some e →
    EvolvesBy ord (e.apply (sys := sys) s) es t →
    EvolvesBy ord s (e :: es) t

theorem EvolvesBy.toEvolves {ord : Ordering (sys := sys)} {s : HGraph V} {es : List sys.Event} {t : HGraph V} :
    ord.EvolvesBy s es t → sys.Evolves s es t := by
  intro h
  induction h with
  | nil s =>
      simpa using (System.Evolves.nil (sys := sys) s)
  | cons e hchoose hrest ih =>
      refine System.Evolves.cons (sys := sys) (e := e) ?_ ih
      exact ord.sound hchoose

end Ordering

end Ordering

end System

end Wolfram
end WPP
end HeytingLean
