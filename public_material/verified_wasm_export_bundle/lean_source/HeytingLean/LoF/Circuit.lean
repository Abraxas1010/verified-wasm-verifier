import HeytingLean.LoF.HeytingCore

/-
# LoF circuits over Ω_R

A small, purely data-level description of LoF "circuits" that we can use as a
low-level state machine for Ω_R theorems.  The semantics live in the LoF
theory; this file just packages named states and transitions in a way that is
easy to export to JSON and visual tools.
-/

namespace HeytingLean
namespace LoF
namespace Circuit

open HeytingLean.LoF

/-- A symbolic fact carried by a circuit state.  For now we keep this
string-based on purpose so that the same structure can be reused across
different Ω_R instances (and rendered directly in visual frontends). -/
structure Fact where
  /-- Human-readable description of the fact, e.g. `a ⊓ b ≤ c`. -/
  desc : String
  deriving Repr

/-- A named state in a LoF circuit.  States are intended to model snapshots of
the Ω_R reasoning context. -/
structure State where
  id    : Nat
  label : String
  facts : List Fact
  deriving Repr

/-- A labelled transition between two circuit states.  The `op` is a short
tag such as `R₁`/`R₂`/`R₃`, while `explain` carries a sentence-level
description suitable for UIs. -/
structure Transition where
  id       : Nat
  fromId   : Nat
  toId     : Nat
  op       : String
  explain  : String
  deriving Repr

/-- A complete LoF circuit: a small state machine whose nodes are Ω_R
contexts and whose edges describe LoF steps between them. -/
structure System where
  name        : String
  summary     : String
  states      : List State
  transitions : List Transition
  deriving Repr

namespace Examples

/-- Low-level LoF circuit for the Heyting residuation law on Ω_R.

This is intentionally symbolic: it does not attempt to re-prove residuation
inside this file, but instead mirrors the blueprint-level R₁/R₂/R₃
decomposition in a state-machine style that is easy to visualise.
-/
def residuation : System :=
  let s0 : State :=
    { id := 0
      label := "Ω_R context"
      facts := [
        ⟨"Fix R : Reentry α and a b c : Ω_R"⟩
      ] }
  let s1 : State :=
    { id := 1
      label := "Assume meet-side inequality"
      facts := [
        ⟨"h₁ : a ⊓ b ≤ c"⟩
      ] }
  let s2 : State :=
    { id := 2
      label := "Apply R₁ (forward residuation)"
      facts := [
        ⟨"From h₁ and Heyting adjunction, obtain h₂ : a ≤ b ⇨ c"⟩
      ] }
  let s3 : State :=
    { id := 3
      label := "Assume implication-side inequality"
      facts := [
        ⟨"h₂ : a ≤ b ⇨ c"⟩
      ] }
  let s4 : State :=
    { id := 4
      label := "Apply R₂ (backward residuation)"
      facts := [
        ⟨"From h₂ and Heyting adjunction, recover h₁ : a ⊓ b ≤ c"⟩
      ] }
  let s5 : State :=
    { id := 5
      label := "Package R₁ and R₂"
      facts := [
        ⟨"R₃ : (a ⊓ b ≤ c) ↔ (a ≤ b ⇨ c)"⟩
      ] }
  { name := "Heyting residuation on Ω_R"
    summary :=
      "Blueprint R₁/R₂/R₃ for a ⊓ b ≤ c ↔ a ≤ b ⇨ c, " ++
      "rendered as a LoF state machine over Ω_R."
    states := [s0, s1, s2, s3, s4, s5]
    transitions := [
      { id := 0
        fromId := 0
        toId := 1
        op := "intro-h₁"
        explain := "Introduce inequality h₁ : a ⊓ b ≤ c in the Ω_R context." },
      { id := 1
        fromId := 1
        toId := 2
        op := "R₁"
        explain := "Use Heyting adjunction to push h₁ across ⇨, deriving h₂ : a ≤ b ⇨ c." },
      { id := 2
        fromId := 2
        toId := 3
        op := "switch-branch"
        explain := "Re-start from the implication side, treating h₂ as the active assumption." },
      { id := 3
        fromId := 3
        toId := 4
        op := "R₂"
        explain := "Use Heyting adjunction in the reverse direction to recover h₁ : a ⊓ b ≤ c." },
      { id := 4
        fromId := 4
        toId := 5
        op := "R₃"
        explain := "Package R₁ and R₂ into R₃ : (a ⊓ b ≤ c) ↔ (a ≤ b ⇨ c)." }
    ] }

end Examples

end Circuit
end LoF
end HeytingLean
