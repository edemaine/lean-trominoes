/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingRecordSourceFieldValueSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierNodeCandidateStreamData

/-! # Source-key crossing fields of the complete carrier-node stream -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierCrossingRecordSourceField

open PaddedSupportedLastRepresentativeEqualityRows

theorem componentValuesWithSentinel_eq_optionalNodeValues
    (field : Field) (descriptors : List RouteDescriptor) :
    ((terminalKeys descriptors).map
        (GuardedPresenceFieldProjector.value false) ++
      (crossingKeys field descriptors).map
        (CarrierKeyFieldProjector.value (keyField field))) ++ [0] =
      (PaddedSupportedLastRepresentativeEqualityRows.values
        (paddedCarrierNodeCandidateStream descriptors)).map
          (optionalNodeValue field) ++ [0] := by
  rw [terminalValues_eq_optionalNodeValues field descriptors,
    crossingValues_eq_optionalNodeValues field descriptors]
  simp [paddedCarrierNodeCandidateStream,
    PaddedSupportedLastRepresentativeEqualityRows.values]

end CarrierCrossingRecordSourceField
end LeanTrominoes.PeriodicOrthocrossing

end
