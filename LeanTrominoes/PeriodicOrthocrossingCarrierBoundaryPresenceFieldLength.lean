/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceFieldData

/-! # Alignment length of the carrier boundary-presence field -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierBoundaryPresenceField

theorem alignedValuesWithSentinel_length_sourceKeyCandidates
    (descriptors : List RouteDescriptor) :
    (alignedValuesWithSentinel descriptors).length =
      (paddedCarrierSourceKeyCandidateStream descriptors).length + 1 := by
  simp [alignedValuesWithSentinel, terminalKeys, crossingKeys,
    PaddedSupportedLastRepresentativeEqualityRows.values,
    paddedCarrierSourceKeyCandidateStream,
    paddedCarrierNodeCandidateStream, Nat.add_assoc]

end CarrierBoundaryPresenceField
end LeanTrominoes.PeriodicOrthocrossing

end
