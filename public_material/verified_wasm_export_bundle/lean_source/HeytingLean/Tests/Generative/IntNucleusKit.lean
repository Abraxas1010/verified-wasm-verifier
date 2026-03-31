import HeytingLean.Generative.IntNucleusKit
import HeytingLean.LoF.IntReentry

open HeytingLean.Generative
open HeytingLean.LoF

-- Sanity checks for IntNucleusKit
variable {α : Type} [PrimaryAlgebra α]
variable (R : IntReentry α)

#check IntNucleusKit.ibreathe (R := R)
#check IntNucleusKit.ibirth (R := R)
#check IntNucleusKit.ioccam (R := R)

