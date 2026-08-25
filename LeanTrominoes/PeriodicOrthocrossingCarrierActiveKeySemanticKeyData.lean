/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyWordData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierNodeCandidateStreamData

/-! # Optional physical keys of the padded carrier-node stream -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierActiveKeyRecipeStream

open PaddedSupportedLastRepresentativeEqualityRows

/-- Optional physical keys aligned with every padded carrier-node slot. -/
def semanticKeys (descriptors : List RouteDescriptor) :
    List (Option CarrierKeyWords.CarrierKey) :=
  (values (paddedCarrierNodeCandidateStream descriptors)).map
    (Option.map CarrierNode.carrierKey)

end CarrierActiveKeyRecipeStream
end LeanTrominoes.PeriodicOrthocrossing

end
