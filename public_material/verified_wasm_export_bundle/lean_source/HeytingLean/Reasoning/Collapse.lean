import HeytingLean.Reasoning.Rules
import HeytingLean.Reasoning.Engine
import HeytingLean.Logic.StageSemantics

/-
Collapse-aware helpers and a Bridge adapter for the reasoning scaffold.
-/

namespace HeytingLean
namespace Reasoning

open HeytingLean.Logic
open HeytingLean.Logic.Stage

variable {α : Type u} [DecidableEq α]

@[simp] def dedup (facts : Array α) : Array α :=
  facts.foldl (init := (#[] : Array α)) (fun acc a => if acc.contains a then acc else acc.push a)

@[simp] def mapFacts (f : α → α) (facts : Array α) : Array α :=
  dedup (facts.map f)

@[simp] def stepCollapsed (collapse : α → α)
    (rules : Array (Rule α)) (facts : Array α) : Array α :=
  let base := facts
  rules.foldl (init := base) (fun acc r =>
    match r.apply acc with
    | some c =>
        let c' := collapse c
        if acc.contains c' then acc else acc.push c'
    | none => acc)

@[simp] def saturateCollapsed (collapse : α → α)
    (rules : Array (Rule α)) (facts : Array α) (maxSteps : Nat := 64) : Array α :=
  let rec go (k : Nat) (f : Array α) : Array α :=
    if k = 0 then f
    else
      let f' := stepCollapsed collapse rules f
      if f'.size = f.size then f else go (k - 1) f'
  go maxSteps (mapFacts collapse facts)

/- Bridge adapter: given a collapse `κ : Ω → Ω` and a bridge `B : Bridge α Ω`,
   induce a collapse on α by staging `κ` across the bridge. -/
@[simp] def collapseViaBridge {α Ω : Type u} [LE α] [LE Ω]
    (B : Bridge α Ω) (κ : Ω → Ω) : α → α :=
  fun x => B.stageCollapse κ x

end Reasoning
end HeytingLean

