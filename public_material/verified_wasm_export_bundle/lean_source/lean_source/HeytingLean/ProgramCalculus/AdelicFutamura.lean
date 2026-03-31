import HeytingLean.ProgramCalculus.AdelicOps
import HeytingLean.ProgramCalculus.Futamura

/-!
# ProgramCalculus.AdelicFutamura

Scaffolding for relating Futamura-style specialization (`Mix`) to adelic-style “depth profiles”
(`AdelicProgramOps.depth : Program → LensID → Int`).

This file deliberately stays interface-first: we record the shape of the expected interaction
as a structure of properties, and provide a couple of small, fully verified “glue” theorems
that are already meaningful for executable QA.
-/

namespace HeytingLean
namespace ProgramCalculus

open HeytingLean.Embeddings

/-- A hypothesis package: specialization reduces (or at least does not increase) per-lens depth. -/
structure AdelicSpecializationModel
    (language : Language)
    (split : SplitInput language.Input)
    (mix : Mix language split)
    (ops : AdelicProgramOps language)
    (residualDepth : mix.Residual → Depth) : Prop where

  /-- Specialization does not increase depth at any lens. -/
  specialize_depth_nonincreasing :
    ∀ (program : language.Program) (static : split.Static) (lens : LensID),
      residualDepth (mix.apply program static) lens ≤ ops.depth program lens

  /-- For a “non-trivial” static input, omega-depth strictly decreases. -/
  specialize_omega_strict :
    ∀ (program : language.Program) (static : split.Static),
      (∃ dyn1 dyn2 : split.Dynamic,
        language.eval program (split.pack static dyn1) ≠
          language.eval program (split.pack static dyn2)) →
        residualDepth (mix.apply program static) LensID.omega <
          ops.depth program LensID.omega

/-- Main theorem: Futamura-1 correctness (re-exported under the “adelic connection” name). -/
theorem futamura_preserves_reconstruction
    {language : Language}
    {split : SplitInput language.Input}
    (mix : Mix language split)
    (model : InterpModel language split)
    (code : split.Static)
    (input : split.Dynamic) :
    mix.evalResidual (compile mix model code) input = model.codeSem code input :=
  compile_correct mix model code input

/-- Normalization does not increase interpreter depth at any lens. -/
theorem depth_interpretation_bound
    {language : Language}
    {split : SplitInput language.Input}
    (ops : AdelicProgramOps language)
    (model : InterpModel language split)
    (lens : LensID) :
    ops.depth (ops.normalize model.interp) lens ≤ ops.depth model.interp lens := by
  simpa using ops.depth_norm model.interp lens

/-- Adelic “restricted product” intuition: only finitely many lenses can differ.

Since `LensID` is finite in this codebase, this is automatic, but it provides a stable named hook. -/
theorem specialization_finite_lens_activity
    {language : Language}
    {split : SplitInput language.Input}
    (mix : Mix language split)
    (ops : AdelicProgramOps language)
    (residualDepth : mix.Residual → Depth)
    (program : language.Program)
    (static : split.Static) :
    {lens : LensID | residualDepth (mix.apply program static) lens ≠ ops.depth program lens}.Finite := by
  classical
  refine
    (Finset.finite_toSet (s :=
      ({LensID.omega, LensID.region, LensID.graph, LensID.clifford, LensID.tensor, LensID.topology, LensID.matula} : Finset LensID))).subset
      ?_
  intro lens _
  cases lens <;> simp

end ProgramCalculus
end HeytingLean
