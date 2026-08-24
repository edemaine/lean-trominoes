/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateMap
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierNodeCandidateStreamData

/-! # Padded compiler-facing carrier rank-data candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows

/-- Preserve every padded node slot and support bit while projecting its
active value to compiler-facing numeric rank data. -/
def paddedCarrierRankDatumCandidateStreamAtPeriod
    (period : Nat) (descriptors : List RouteDescriptor) :
    List (Candidate CarrierNodeRankDatum) :=
  (paddedCarrierNodeCandidateStream descriptors).map
    (Candidate.mapValue (carrierNodeRankDatumAtPeriod period))

end LeanTrominoes.PeriodicOrthocrossing
