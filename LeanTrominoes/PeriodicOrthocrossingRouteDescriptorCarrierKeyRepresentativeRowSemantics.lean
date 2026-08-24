/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateRepresentativeRowSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyWordSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyCandidateStreamSupport
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyRepresentativeRowData

/-! # Semantics of padded carrier-key representative rows -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedCandidateWords
open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorPairAffine

/-- Under the route-stream invariants and exact terminal projection, the
generic guarded-word pipeline returns precisely the support-aware selected
rows of the complete padded carrier candidate stream. -/
theorem paddedCarrierKeyRepresentativeRows_eq_selectedRows
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
    paddedCarrierKeyRepresentativeRows descriptors =
      selectedRows (paddedCarrierKeyCandidateStream descriptors) := by
  unfold paddedCarrierKeyRepresentativeRows
  apply representativeRows_eq_selectedRows
    CarrierKeyWords.word CarrierKeyWords.word_injective
    (occurrenceTerminalCarrierKeys
      (routeDescriptorNeighborOccurrences descriptors))
  have candidateCorrect := paddedCarrierKeyCandidateStream_correctSupport
    descriptors selfIndexed localShapes terminalValues
  intro candidate candidateMember
  have correct := candidateCorrect candidate candidateMember
  exact correct.trans (by
    by_cases member : candidate.value ∈
        (occurrenceTerminalCarrierKeys
          (routeDescriptorNeighborOccurrences descriptors)).map some <;>
      simp [member])

end LeanTrominoes.PeriodicOrthocrossing
