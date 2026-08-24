/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCarrierSegmentPredicateData

/-! # Activation bits for terminal carrier-key blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

/-- One activation bit per fixed terminal-key template block. -/
def terminalCarrierKeyActivations
    (tokens : List RouteDescriptorPairFieldTags.Token) : List Bool :=
  carrierSegmentPredicates.map fun predicate =>
    predicate.evalTokens tokens

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
