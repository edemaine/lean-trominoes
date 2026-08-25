/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingRecordSourceFieldData

/-! # Alignment length of source-key crossing fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierCrossingRecordSourceField

theorem alignedValuesWithSentinel_length_sourceKeyCandidates
    (field : Field) (descriptors : List RouteDescriptor) :
    (alignedValuesWithSentinel field descriptors).length =
      (paddedCarrierSourceKeyCandidateStream descriptors).length + 1 := by
  simp [alignedValuesWithSentinel, terminalKeys, crossingKeys,
    PaddedSupportedLastRepresentativeEqualityRows.values,
    paddedCarrierSourceKeyCandidateStream,
    paddedCarrierNodeCandidateStream, Nat.add_assoc]

end CarrierCrossingRecordSourceField
end LeanTrominoes.PeriodicOrthocrossing

end
