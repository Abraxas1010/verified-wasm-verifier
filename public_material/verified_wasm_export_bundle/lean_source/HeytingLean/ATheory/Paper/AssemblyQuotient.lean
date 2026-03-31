import HeytingLean.ATheory.Paper.AssemblyIndex

namespace HeytingLean
namespace ATheory
namespace Paper

open scoped Classical

namespace AssemblySpace

variable (S : AssemblySpace)

/-- Quotient an assembly space by an equivalence relation on objects.

This is a thin wrapper that lifts `U` and `J` along `Quotient.mk`.
-/
def quotient (r : Setoid S.Ω) : AssemblySpace where
  Ω := Quotient r
  U := {q | ∃ x ∈ S.U, Quotient.mk r x = q}
  J := fun qx qy qz =>
    ∃ x y z,
      Quotient.mk r x = qx ∧
      Quotient.mk r y = qy ∧
      Quotient.mk r z = qz ∧
      S.J x y z

namespace Quotient

variable {S} {r : Setoid S.Ω}

@[simp] lemma mk_mem_U {x : S.Ω} (hx : x ∈ S.U) :
    Quotient.mk r x ∈ (AssemblySpace.quotient (S := S) r).U :=
  ⟨x, hx, rfl⟩

private def liftSet (A : Set S.Ω) : Set (Quotient r) :=
  {q | ∃ x ∈ A, Quotient.mk r x = q}

private def mapStep (s : Step (S := S)) : Step (S := AssemblySpace.quotient (S := S) r) where
  x := Quotient.mk r s.x
  y := Quotient.mk r s.y
  z := Quotient.mk r s.z
  ok := ⟨s.x, s.y, s.z, rfl, rfl, rfl, s.ok⟩

private lemma map_wf_aux (A : Set S.Ω) :
    ∀ {steps : List (Step (S := S))},
      WellFormedFrom (S := S) A steps →
      WellFormedFrom (S := AssemblySpace.quotient (S := S) r) (liftSet (r := r) A)
        (steps.map (mapStep (S := S) (r := r))) := by
  intro steps
  induction steps generalizing A with
  | nil =>
      intro wf
      simp
  | cons s ss ih =>
      intro wf
      rcases wf with ⟨hsUse, wfTail⟩
      have hsUse' : (mapStep (S := S) (r := r) s).usable
          (S := AssemblySpace.quotient (S := S) r) (liftSet (r := r) A) := by
        refine ⟨?_, ?_⟩
        · exact ⟨s.x, hsUse.1, rfl⟩
        · exact ⟨s.y, hsUse.2, rfl⟩
      have ih' :
          WellFormedFrom (S := AssemblySpace.quotient (S := S) r)
            (liftSet (r := r) (Set.insert s.z A))
            (ss.map (mapStep (S := S) (r := r))) :=
        ih (A := Set.insert s.z A) wfTail
      -- Rewrite the post-step available set.
      have hLift :
          liftSet (r := r) (Set.insert s.z A) =
            Set.insert (Quotient.mk r s.z) (liftSet (r := r) A) := by
        ext q
        constructor
        · intro hq
          rcases hq with ⟨x, hx, rfl⟩
          rcases hx with rfl | hx
          · exact Or.inl rfl
          · exact Or.inr ⟨x, hx, rfl⟩
        · intro hq
          rcases hq with rfl | hq
          · exact ⟨s.z, Or.inl rfl, rfl⟩
          · rcases hq with ⟨x, hx, rfl⟩
            exact ⟨x, Or.inr hx, rfl⟩
      refine And.intro hsUse' ?_
      simpa [WellFormedFrom, hLift] using ih'

private lemma map_wf (p : AssemblyPath (S := S) (z := (z : S.Ω))) :
    WellFormedFrom (S := AssemblySpace.quotient (S := S) r)
      (AssemblySpace.quotient (S := S) r).U
      (p.steps.map (mapStep (S := S) (r := r))) := by
  have hU : liftSet (r := r) S.U = (AssemblySpace.quotient (S := S) r).U := by
    ext q
    constructor
    · intro hq
      rcases hq with ⟨x, hx, rfl⟩
      exact mk_mem_U (S := S) (r := r) hx
    · intro hq
      rcases hq with ⟨x, hx, hxq⟩
      refine ⟨x, hx, hxq⟩
  simpa [hU] using map_wf_aux (S := S) (r := r) (A := S.U) p.wf

private lemma map_ok_out (p : AssemblyPath (S := S) (z := (z : S.Ω))) :
    ((p.steps.map (mapStep (S := S) (r := r))) = [] ∧
        Quotient.mk r z ∈ (AssemblySpace.quotient (S := S) r).U) ∨
      (∃ s,
        (p.steps.map (mapStep (S := S) (r := r))).getLast? = some s ∧
          s.z = Quotient.mk r z) := by
  rcases p.ok_out with ⟨hsteps, hzU⟩ | ⟨s, hsLast, hsZ⟩
  · left
    constructor
    · simp [hsteps]
    · simpa using mk_mem_U (S := S) (r := r) hzU
  · right
    rcases (List.getLast?_eq_some_iff.mp hsLast) with ⟨ys, hys⟩
    refine ⟨mapStep (S := S) (r := r) s, ?_, ?_⟩
    ·
      have : p.steps.map (mapStep (S := S) (r := r)) =
          (ys.map (mapStep (S := S) (r := r))) ++ [mapStep (S := S) (r := r) s] := by
        simp [hys, List.map_append]
      exact (List.getLast?_eq_some_iff.mpr ⟨ys.map (mapStep (S := S) (r := r)), this⟩)
    · simp [mapStep, hsZ]

/-- Map an assembly path in `S` to an assembly path in the quotient space. -/
noncomputable def mapPath (z : S.Ω) (p : AssemblyPath (S := S) z) :
    AssemblyPath (S := AssemblySpace.quotient (S := S) r) (Quotient.mk r z) :=
  { steps := p.steps.map (mapStep (S := S) (r := r))
    wf := by
      -- The binder form of `map_wf` avoids rewriting `z` in the binder.
      simpa using (map_wf (S := S) (r := r) (z := z) p)
    ok_out := by
      simpa using (map_ok_out (S := S) (r := r) (z := z) p) }

end Quotient

namespace Closed

variable {S : AssemblySpace}

/-- If an assembly space is closed, then its quotient is also closed. -/
noncomputable def quotient (hC : Closed S) (r : Setoid S.Ω) :
    Closed (AssemblySpace.quotient (S := S) r) := by
  classical
  refine ⟨fun q => ?_⟩
  refine Quotient.inductionOn q (fun z => ?_) 
  rcases hC.exists_path z with ⟨p⟩
  exact ⟨AssemblySpace.Quotient.mapPath (S := S) (r := r) z p⟩

end Closed

namespace AssemblyIndex

variable {S : AssemblySpace}

lemma assemblyIndex_quotient_le (hC : Closed S) (r : Setoid S.Ω) (z : S.Ω) :
    AssemblyIndex.assemblyIndex (S := AssemblySpace.quotient (S := S) r)
        (hC := Closed.quotient (S := S) hC r) (Quotient.mk r z)
      ≤ AssemblyIndex.assemblyIndex (S := S) (hC := hC) z := by
  classical
  rcases assemblyIndex_spec (S := S) (hC := hC) z with ⟨p, hp⟩
  let p' := AssemblySpace.Quotient.mapPath (S := S) (r := r) z p
  have hmin :
      AssemblyIndex.assemblyIndex (S := AssemblySpace.quotient (S := S) r)
          (hC := Closed.quotient (S := S) hC r) (Quotient.mk r z)
        ≤ p'.len :=
    assemblyIndex_le_of_path
      (S := AssemblySpace.quotient (S := S) r)
      (hC := Closed.quotient (S := S) hC r)
      (z := Quotient.mk r z) p'
  have hlen : p'.len = p.len := by
    simp [p', AssemblySpace.Quotient.mapPath, AssemblyPath.len]
  simpa [hp, hlen] using hmin

end AssemblyIndex

end AssemblySpace

end Paper
end ATheory
end HeytingLean
