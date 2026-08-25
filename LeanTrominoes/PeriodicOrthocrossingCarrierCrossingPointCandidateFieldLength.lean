/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingPointCandidateAlignmentSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierSourceKeyCandidateStreamData

/-! # Alignment length of crossing-point candidate fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierCrossingPointCandidateFieldStream

open CarrierCrossingPointField

theorem valuesWithSentinel_length_sourceKeyCandidates
    (field : Field) (descriptors : List RouteDescriptor) :
    (valuesWithSentinel field descriptors).length =
      (paddedCarrierSourceKeyCandidateStream descriptors).length + 1 := by
  have lengthEq :=
    (values_forall₂_paddedCarrierNodeCandidateStream
      field descriptors).length_eq
  simpa [valuesWithSentinel, paddedCarrierSourceKeyCandidateStream] using
    lengthEq.symm

end CarrierCrossingPointCandidateFieldStream
end LeanTrominoes.PeriodicOrthocrossing
