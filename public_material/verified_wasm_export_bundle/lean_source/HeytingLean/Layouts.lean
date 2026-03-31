import HeytingLean.Layouts.Flat.Basic
import HeytingLean.Layouts.Flat.Tractable
import HeytingLean.Layouts.Flat.Operations.Coalesce
import HeytingLean.Layouts.Flat.Operations.Complement
import HeytingLean.Layouts.Flat.Operations.Compose
import HeytingLean.Layouts.Tuple.Category
import HeytingLean.Layouts.Tuple.Functor
import HeytingLean.Layouts.Tuple.ToLayout
import HeytingLean.Layouts.Tuple.Realization
import HeytingLean.Layouts.Nested.Profile
import HeytingLean.Layouts.Nested.Refinement
import HeytingLean.Layouts.Nested.NestCategory
import HeytingLean.Layouts.Nested.PullbackPushforward
import HeytingLean.Layouts.Nested.Operations.DivisionProduct
import HeytingLean.Layouts.Nested.Operations.ComposeAlgorithm

/-!
# Layout categories (CuTe)

Entry point for the CuTe layout-categories development in HeytingLean.

This currently includes:
- the *flat* layer (`Tuple` + encoded flat layouts), and
- nested tuple/profile infrastructure plus executable mutual refinement, pullback/pushforward,
  weak composition, and logical division/product operations.
-/
