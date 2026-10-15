/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Active.PeriodicOrthocrossingCarrierActiveKeySemanticKeyData
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Key.PeriodicOrthocrossingCarrierKeyRouteFieldProjectorWordSemantics
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Source.PeriodicOrthocrossingCarrierSourceKeyRepresentativeLookupData
import LeanTrominoes.Graphs.Drawings.Orthogonal.Route.PeriodicOrthocrossingRouteDescriptorCarrierNodeCandidateStreamData

/-! # Selected carrier-key route field of carrier rank data -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyRouteField

open PaddedSupportedLastRepresentativeEqualityRows

/-- One route-index value for every padded carrier-node slot, followed by
the rejection sentinel required by representative lookup. -/
def alignedValuesWithSentinel
    (descriptors : List RouteDescriptor) : List Nat :=
  (CarrierActiveKeyRecipeStream.semanticKeys descriptors).map
      CarrierKeyRouteFieldProjector.value ++
    [0]

/-- Look up the route index at every compact carrier-node representative. -/
def values (descriptors : List RouteDescriptor) : List Nat :=
  CarrierSourceKeyRepresentativeLookup.values
    alignedValuesWithSentinel descriptors

end CarrierRankKeyRouteField
end LeanTrominoes.PeriodicOrthocrossing

end
