namespace HeytingLean.HeytingVeil.Route

inductive BackendRoute
  | lambdaIRMiniCC
  | lambdaIROnly
  | miniCOnly
  deriving Repr, DecidableEq, Inhabited

structure RouteRecord where
  route : BackendRoute
  routeClassId : String := "unknown"
  preservationWitnessIds : List String
  previewPromotionReady : Bool := false
  previewPromotionCertified : Bool := false
  witnessTier : String := "minimal"
  certifiedRequested : Bool := false
  deriving Repr, DecidableEq

end HeytingLean.HeytingVeil.Route
