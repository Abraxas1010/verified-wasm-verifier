/-
Moduli scaffold: genus/punctures and a simple sewing operation.
-/

namespace HeytingLean
namespace Physics
namespace String

structure RiemannSurface where
  genus : Nat
  punctures : Nat
deriving Repr

@[simp] def sew (sig1 sig2 : RiemannSurface) : RiemannSurface :=
  -- Add genera and punctures, then connect one puncture if possible
  let p := if sig1.punctures = 0 || sig2.punctures = 0 then 0 else 1
  { genus := sig1.genus + sig2.genus
  , punctures := sig1.punctures + sig2.punctures - p }

end String
end Physics
end HeytingLean
