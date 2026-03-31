import Mathlib.Data.List.Perm.Basic
import HeytingLean.ATheory.Paper.AssemblyIndex

namespace HeytingLean
namespace ATheory
namespace Paper

open scoped Classical

/-!
# A rule+equivalence assembly space for strings

This file provides a concrete Assembly Theory model where objects are strings (`List Atom`).

* **Equivalence layer**: joins are defined up to permutation (`List.Perm`).
* **Rule layer**: a predicate `Allowed x y` gates whether a join is permitted.

This is intentionally *not* claiming we can compute the exact minimal `assemblyIndex` for
general strings (which can be hard). Instead we provide:

* closure (`Closed`) under a *total* rule predicate;
* a bridge lemma: any syntax-tree presentation `o : Obj Atom` gives an upper bound
  `assemblyIndex (flatten o) ≤ Obj.dagJoinCount o`.
-/

namespace StringPerm

universe u
variable {Atom : Type u}

open Paper.AssemblySpace
open HeytingLean.ATheory

/-- Strings as an assembly space, with rules + permutation-equivalence on joins.

`Allowed` is the rule predicate; the join relation is:

`J x y z := Allowed x y ∧ Perm (x ++ y) z`.
-/
def spaceRules (Allowed : List Atom → List Atom → Prop) : Paper.AssemblySpace where
  Ω := List Atom
  U := {xs | xs = [] ∨ ∃ a, xs = [a]}
  J := fun x y z => Allowed x y ∧ List.Perm (x ++ y) z

/-- Default “total rule” instance: every pair is joinable. -/
def space : Paper.AssemblySpace :=
  spaceRules (Atom := Atom) (fun _ _ => True)

namespace spaceRules

variable {Allowed : List Atom → List Atom → Prop}

@[simp] lemma mem_U_nil : ([] : List Atom) ∈ (spaceRules (Atom := Atom) Allowed).U :=
  Or.inl rfl

@[simp] lemma mem_U_singleton (a : Atom) : ([a] : List Atom) ∈ (spaceRules (Atom := Atom) Allowed).U :=
  Or.inr ⟨a, rfl⟩

/-- Closure holds if the rule predicate is total. -/
noncomputable def closed_of_total (hAllowed : ∀ x y, Allowed x y) :
    Closed (spaceRules (Atom := Atom) Allowed) := by
  classical
  refine ⟨fun z => ?_⟩
  -- A simple closure witness: for `a :: xs`, build `xs` first, then join `[a]` with `xs`.
  classical
  refine ⟨?_
  ⟩
  -- Noncomputable recursion is fine since `assemblyIndex` itself is noncomputable.
  classical
  let rec mkPath : ∀ z : List Atom, AssemblyPath (S := spaceRules (Atom := Atom) Allowed) z
    | [] =>
        AssemblyPath.primitive (S := spaceRules (Atom := Atom) Allowed)
          (z := []) (mem_U_nil (Atom := Atom) (Allowed := Allowed))
    | [a] =>
        AssemblyPath.primitive (S := spaceRules (Atom := Atom) Allowed)
          (z := [a]) (mem_U_singleton (Atom := Atom) (Allowed := Allowed) a)
    | a :: b :: xs => by
        let pTail : AssemblyPath (S := spaceRules (Atom := Atom) Allowed) (b :: xs) := mkPath (b :: xs)
        have hUsub : (spaceRules (Atom := Atom) Allowed).U ⊆
            availableAfter (S := spaceRules (Atom := Atom) Allowed)
              (spaceRules (Atom := Atom) Allowed).U pTail.steps :=
          subset_availableAfter (S := spaceRules (Atom := Atom) Allowed)
            (A := (spaceRules (Atom := Atom) Allowed).U) pTail.steps
        have hTailAvail : (b :: xs) ∈
            availableAfter (S := spaceRules (Atom := Atom) Allowed)
              (spaceRules (Atom := Atom) Allowed).U pTail.steps :=
          AssemblyPath.mem_availableAfter (S := spaceRules (Atom := Atom) Allowed) (z := (b :: xs)) pTail
        have hHeadAvail : ([a] : List Atom) ∈
            availableAfter (S := spaceRules (Atom := Atom) Allowed)
              (spaceRules (Atom := Atom) Allowed).U pTail.steps :=
          hUsub (mem_U_singleton (Atom := Atom) (Allowed := Allowed) a)
        let finalStep : Step (spaceRules (Atom := Atom) Allowed) :=
          { x := [a]
            y := (b :: xs)
            z := (a :: b :: xs)
            ok := by
              refine ⟨hAllowed _ _, ?_⟩
              simp }
        have wfFinal : WellFormedFrom (S := spaceRules (Atom := Atom) Allowed)
            (availableAfter (S := spaceRules (Atom := Atom) Allowed)
              (spaceRules (Atom := Atom) Allowed).U pTail.steps)
            [finalStep] := by
          simp [WellFormedFrom, Step.usable, finalStep, hHeadAvail, hTailAvail]
        have wfAll : WellFormedFrom (S := spaceRules (Atom := Atom) Allowed)
            (spaceRules (Atom := Atom) Allowed).U (pTail.steps ++ [finalStep]) :=
          wellFormedFrom_append (S := spaceRules (Atom := Atom) Allowed)
            (A := (spaceRules (Atom := Atom) Allowed).U)
            (xs := pTail.steps) (ys := [finalStep]) pTail.wf (by simpa using wfFinal)
        exact
          { steps := pTail.steps ++ [finalStep]
            wf := wfAll
            ok_out := Or.inr (by
              refine ⟨finalStep, ?_, rfl⟩
              simp) }
  exact mkPath z

end spaceRules

namespace space

@[simp] lemma mem_U_nil : ([] : List Atom) ∈ (space (Atom := Atom)).U :=
  spaceRules.mem_U_nil (Atom := Atom) (Allowed := fun _ _ => True)

@[simp] lemma mem_U_singleton (a : Atom) : ([a] : List Atom) ∈ (space (Atom := Atom)).U :=
  spaceRules.mem_U_singleton (Atom := Atom) (Allowed := fun _ _ => True) a

noncomputable def closed : Closed (space (Atom := Atom)) :=
  spaceRules.closed_of_total (Atom := Atom) (Allowed := fun _ _ => True) (by intro x y; trivial)

end space

/-! ## Flattening syntax objects into strings -/

def flatten : Obj Atom → List Atom
  | Obj.base a => [a]
  | Obj.join l r => flatten l ++ flatten r

@[simp] lemma flatten_base (a : Atom) : flatten (Atom := Atom) (Obj.base a) = [a] := rfl

@[simp] lemma flatten_join (l r : Obj Atom) :
    flatten (Atom := Atom) (Obj.join l r) = flatten (Atom := Atom) l ++ flatten (Atom := Atom) r := rfl

/-! ## Mapping ObjSyntax paths to StringPerm paths -/

namespace ObjSyntaxMap

open ObjSyntax

private def mapStep (s : Step (ObjSyntax.space (Atom := Atom))) :
    Step (space (Atom := Atom)) :=
  { x := flatten (Atom := Atom) s.x
    y := flatten (Atom := Atom) s.y
    z := flatten (Atom := Atom) s.z
    ok := by
      -- In `ObjSyntax.space`, `s.ok : s.z = Obj.join s.x s.y`.
      refine ⟨True.intro, ?_⟩
      have hz : flatten (Atom := Atom) s.z =
          flatten (Atom := Atom) s.x ++ flatten (Atom := Atom) s.y := by
        have hz0 :
            flatten (Atom := Atom) s.z =
              flatten (Atom := Atom) (Obj.join s.x s.y) :=
          congrArg (fun t => flatten (Atom := Atom) t) s.ok
        simp [flatten] at hz0
        exact hz0
      -- Goal is `Perm (flatten x ++ flatten y) (flatten z)`.
      simp [hz]
  }

private lemma map_wf_aux (A : Set (Obj Atom)) (A' : Set (List Atom))
    (hAA' : ∀ t, t ∈ A → flatten (Atom := Atom) t ∈ A') :
    ∀ {steps : List (Step (ObjSyntax.space (Atom := Atom)))},
      WellFormedFrom (S := ObjSyntax.space (Atom := Atom)) A steps →
      WellFormedFrom (S := space (Atom := Atom)) A' (steps.map mapStep) := by
  intro steps
  induction steps generalizing A A' with
  | nil =>
      intro wf
      simp
  | cons s ss ih =>
      intro wf
      rcases wf with ⟨hsUse, wfTail⟩
      have hsUse' : (mapStep (Atom := Atom) s).usable (S := space (Atom := Atom)) A' :=
        ⟨hAA' _ hsUse.1, hAA' _ hsUse.2⟩
      have hAA'' :
          ∀ t, t ∈ Set.insert s.z A →
            flatten (Atom := Atom) t ∈ Set.insert (flatten (Atom := Atom) s.z) A' := by
        intro t ht
        rcases ht with rfl | ht
        · exact Or.inl rfl
        · exact Or.inr (hAA' _ ht)
      exact And.intro hsUse' (ih (A := Set.insert s.z A)
        (A' := Set.insert (flatten (Atom := Atom) s.z) A') hAA'' wfTail)

private lemma map_wf (p : AssemblyPath (S := ObjSyntax.space (Atom := Atom)) (o : Obj Atom)) :
    WellFormedFrom (S := space (Atom := Atom)) (space (Atom := Atom)).U (p.steps.map mapStep) := by
  -- Base mapping property: primitives map to singletons.
  have hU : ∀ t, t ∈ (ObjSyntax.space (Atom := Atom)).U →
      flatten (Atom := Atom) t ∈ (space (Atom := Atom)).U := by
    intro t ht
    rcases ht with ⟨a, rfl⟩
    simp
  exact map_wf_aux (Atom := Atom)
    (A := (ObjSyntax.space (Atom := Atom)).U)
    (A' := (space (Atom := Atom)).U) hU p.wf

private lemma map_ok_out
    (p : AssemblyPath (S := ObjSyntax.space (Atom := Atom)) (o : Obj Atom)) :
    ((p.steps.map mapStep) = [] ∧ flatten (Atom := Atom) o ∈ (space (Atom := Atom)).U) ∨
      (∃ s, (p.steps.map mapStep).getLast? = some s ∧ s.z = flatten (Atom := Atom) o) := by
  rcases p.ok_out with ⟨hsteps, hoU⟩ | ⟨s, hsLast, hsZ⟩
  · left
    constructor
    · simp [hsteps]
    · rcases hoU with ⟨a, ha⟩
      subst ha
      simp
  · right
    -- Convert `getLast? = some s` into a `ys ++ [s]` decomposition, then map.
    rcases (List.getLast?_eq_some_iff.mp hsLast) with ⟨ys, hys⟩
    refine ⟨mapStep (Atom := Atom) s, ?_, ?_⟩
    ·
      have : (p.steps.map mapStep) = (ys.map mapStep) ++ [mapStep (Atom := Atom) s] := by
        simp [hys, List.map_append]
      -- Now the last element is `mapStep s`.
      exact (List.getLast?_eq_some_iff.mpr ⟨ys.map mapStep, this⟩)
    ·
      -- Output equality.
      simp [mapStep, hsZ]

/-- Map an ObjSyntax assembly path to a StringPerm-space path by flattening. -/
noncomputable def mapPath
    (p : AssemblyPath (S := ObjSyntax.space (Atom := Atom)) (o : Obj Atom)) :
    AssemblyPath (S := space (Atom := Atom)) (flatten (Atom := Atom) o) :=
  { steps := p.steps.map mapStep
    wf := map_wf (Atom := Atom) p
    ok_out := map_ok_out (Atom := Atom) p }

end ObjSyntaxMap

/-! ## Goal B bridge theorem -/

lemma assemblyIndex_flatten_le_dagJoinCount [DecidableEq Atom] (o : Obj Atom) :
    AssemblyIndex.assemblyIndex (S := space (Atom := Atom)) (hC := space.closed (Atom := Atom))
        (flatten (Atom := Atom) o)
      ≤ Obj.dagJoinCount o := by
  classical
  -- Pick a minimal ObjSyntax path for `o` and map it.
  rcases
      AssemblyIndex.assemblyIndex_spec
        (S := ObjSyntax.space (Atom := Atom))
        (hC := ObjSyntax.space.closed (Atom := Atom)) o with
    ⟨p, hp⟩
  have hpLen : p.len = Obj.dagJoinCount o := by
    -- `p.len = assemblyIndex o = dagJoinCount o`.
    calc
      p.len =
          AssemblyIndex.assemblyIndex (S := ObjSyntax.space (Atom := Atom))
            (hC := ObjSyntax.space.closed (Atom := Atom)) o := hp
      _ = Obj.dagJoinCount o :=
          ObjSyntax.space.assemblyIndex_eq_dagJoinCount (Atom := Atom) (o := o)
  let p' := ObjSyntaxMap.mapPath (Atom := Atom) (o := o) p
  have hmin :
      AssemblyIndex.assemblyIndex (S := space (Atom := Atom)) (hC := space.closed (Atom := Atom))
          (flatten (Atom := Atom) o)
        ≤ p'.len :=
    AssemblyIndex.assemblyIndex_le_of_path
      (S := space (Atom := Atom)) (hC := space.closed (Atom := Atom)) (z := flatten (Atom := Atom) o) p'
  -- `p'.len = p.len`.
  have hlen : p'.len = p.len := by
    simp [p', ObjSyntaxMap.mapPath, AssemblyPath.len]
  -- Conclude.
  calc
    AssemblyIndex.assemblyIndex (S := space (Atom := Atom)) (hC := space.closed (Atom := Atom))
        (flatten (Atom := Atom) o)
        ≤ p'.len := hmin
    _ = p.len := hlen
    _ = Obj.dagJoinCount o := hpLen

end StringPerm

end Paper
end ATheory
end HeytingLean
