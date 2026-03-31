import HeytingLean.ProgramCalculus.AdelicOps
import HeytingLean.ProgramCalculus.AdelicOpsInstances.SKYAdelic

/-!
# ProgramCalculus.AdelicOpsInstances

Concrete (baseline) instantiations of `AdelicProgramOps`.

The first goal is to make the interface *usable* in executable demos without committing
to a full “adelic arithmetic = program transformation” semantics yet.  We therefore
provide a trivial, law-abiding instance that can be swapped out later.
-/

namespace HeytingLean
namespace ProgramCalculus

open HeytingLean.Embeddings

/-- A baseline `AdelicProgramOps` instance that satisfies the laws trivially.

This is a *placeholder semantics*:
* `depth` is identically `0`,
* `mul`/`add` ignore their second argument,
* `normalize` is `id`,
* `renormDiv a e = (a, a)`.

It is useful for wiring and runtime harnesses; it does **not** validate any substantive
adelic hypothesis. -/
def trivialAdelicProgramOps (language : Language) : AdelicProgramOps language :=
  let depth : language.Program → Depth := fun _ _ => 0
  let mul : language.Program → language.Program → language.Program := fun a _ => a
  let add : language.Program → language.Program → language.Program := fun a _ => a
  let normalize : language.Program → language.Program := fun a => a
  let renormDiv : language.Program → language.Program → language.Program × language.Program :=
    fun a _ => (a, a)
  { depth := depth
    mul := mul
    add := add
    normalize := normalize
    renormDiv := renormDiv
    depth_mul := by
      intro a b lens
      simp [depth, mul]
    depth_add := by
      intro a b lens
      simp [depth, add]
    depth_norm := by
      intro a lens
      simp [depth, normalize]
    div_reconstruct := by
      intro a e
      simp [renormDiv, ObsEq, mul, add] }

end ProgramCalculus
end HeytingLean
