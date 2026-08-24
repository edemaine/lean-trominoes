/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyCandidateStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyCandidateStreamSupport
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyCandidateStreamSupport

/-! # Support of complete padded route-descriptor carrier candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorPairAffine

/-- If the terminal prefix projects to the semantic terminal stream, then
the complete terminal-plus-crossing padded stream has exact support relative
to that semantic base. -/
theorem paddedCarrierKeyCandidateStream_correctSupport
    (descriptors : List RouteDescriptor)
    (selfIndexed : ∀ tagged ∈ descriptors.zipIdx,
      tagged.1.edgeIndex = tagged.2)
    (localShapes : ∀ descriptor ∈ descriptors,
      ∃ shape : RouteShape, shape.Matches descriptor)
    (terminalValues :
      (paddedTerminalCarrierKeyCandidateStream descriptors).filterMap
          Candidate.value =
        occurrenceTerminalCarrierKeys
          (routeDescriptorNeighborOccurrences descriptors)) :
    CorrectSupport
      (occurrenceTerminalCarrierKeys
        (routeDescriptorNeighborOccurrences descriptors))
      (paddedCarrierKeyCandidateStream descriptors) := by
  have terminalCorrect :=
    paddedTerminalCarrierKeyCandidateStream_correctSupport descriptors
  rw [terminalValues] at terminalCorrect
  have crossingCorrect :=
    RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierKeyCandidateStream_correctSupport
      descriptors selfIndexed localShapes
  intro candidate candidateMember
  unfold paddedCarrierKeyCandidateStream at candidateMember
  rcases List.mem_append.mp candidateMember with
    terminalMember | crossingMember
  · exact terminalCorrect candidate terminalMember
  · exact crossingCorrect candidate crossingMember

end LeanTrominoes.PeriodicOrthocrossing
