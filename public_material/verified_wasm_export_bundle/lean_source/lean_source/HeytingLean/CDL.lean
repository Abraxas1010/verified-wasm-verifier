import HeytingLean.CDL.Para.Type
import HeytingLean.CDL.Para.Bicategory
import HeytingLean.CDL.Para.ParaT
import HeytingLean.CDL.StrongMonad
import HeytingLean.CDL.Para.ArchitectureGraph
import HeytingLean.CDL.RNucleusMonad
import HeytingLean.CDL.LaxAlgebraComonoid
import HeytingLean.CDL.LaxAlgebraDerived
import HeytingLean.CDL.Coalgebra.Mealy
import HeytingLean.CDL.Coalgebra.MealyBridge
import HeytingLean.CDL.OrbitWeightTying
import HeytingLean.CDL.TrainingStep
import HeytingLean.CDL.Examples.FoldingRNN

/-!
# CDL (umbrella)

This namespace hosts a Lean-realistic integration of key constructs from
**Categorical Deep Learning** (Gavranović et al., arXiv:2402.15332v2):

- `Para(Type)` parametric maps and reparameterizations,
- a minimal strong-monad interface and the `Para(T)` lift,
- lax-algebra-shaped comonoid data giving weight tying maps `Δ`,
- orbit-based tying via quotients by `R`-normalization,
- a small mechanized unrolling example (2-step folding RNN).
-/
