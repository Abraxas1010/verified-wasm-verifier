import HeytingLean.Moonshine.Borcherds.Denominator

set_option autoImplicit false

namespace HeytingLean.Moonshine

/--
Gate-E replication interface.

This packages a replication predicate together with the fact that denominator identities
produce replication for all Monster elements.
-/
structure ReplicationData where
  D : DenominatorIdentityData
  replicable : D.B.C.S.M → Prop
  replication_from_denominator : ∀ g : D.B.C.S.M, replicable g

namespace ReplicationData

theorem all_replicable (R : ReplicationData) (g : R.D.B.C.S.M) : R.replicable g :=
  R.replication_from_denominator g

theorem one_replicable (R : ReplicationData) : R.replicable (1 : R.D.B.C.S.M) :=
  R.replication_from_denominator 1

end ReplicationData

end HeytingLean.Moonshine
