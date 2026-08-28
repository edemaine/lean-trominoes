/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateRepresentativeRowSemantics
import LeanTrominoes.PaddedSupportedCandidateSelfSupport
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingCompactAtomWordSourceData
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingLeftSourceKeyInjectivity
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyRepresentativeCompiler

/-! # Semantics of common-shift source-key representatives -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingShiftLeftSourceKeyRepresentatives

open RouteDescriptorOccurrenceSlotBinaryWords
open PaddedSupportedLastRepresentativeEqualityRows

theorem candidateList_supported_eq_isSome
    (descriptors : List RouteDescriptor) :
    ∀ candidate ∈ candidateList descriptors,
      candidate.supported = candidate.value.isSome := by
  exact CanonicalCrossingShiftLeftSourceKeyStream.candidates_supported_eq_isSome
    _

/-- The compiled rows are the exact self-supported last representatives of
the complete fixed candidate list. -/
theorem representativeRows_eq_selectedRows
    (descriptors : List RouteDescriptor) :
    representativeRows descriptors =
      selectedRows (candidateList descriptors) := by
  unfold representativeRows
  apply PaddedSupportedCandidateWords.representativeRows_eq_selectedRows
    CarrierNodeSourceKeys.word CarrierNodeSourceKeys.word_injective
    ((candidateList descriptors).filterMap Candidate.value)
  exact correctSupport_filterMap_of_supported_eq_isSome
    (candidateList descriptors)
    (candidateList_supported_eq_isSome descriptors)

/-- For a valid numeric descriptor presentation, selected source-pair values
are exactly the compact image of the canonicalized crossing halo. -/
theorem values_eq_canonicalizedCrossingPairs
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    (descriptors : List RouteDescriptor)
    (selfIndexed : RouteDescriptorList.SelfIndexed descriptors)
    (commonPeriod :
      ∀ descriptor ∈ descriptors,
        descriptor.gridSize = drawingGridSize graph)
    (localShapes :
      ∀ descriptor ∈ descriptors,
        RouteDescriptorPairAffine.RouteDescriptor.HasLocalShape descriptor)
    (occurrencesEq :
      routeDescriptorNeighborOccurrences descriptors =
        neighborOccurrences graph) :
    values descriptors =
      (occurrencePairCanonicalizedCrossingHaloAtPeriod
        (drawingGridSize graph)
        (routeDescriptorNeighborOccurrences descriptors)).map
          RetainedCompactAtomWords.crossingPair := by
  unfold values candidateList
  rw [CanonicalCrossingShiftLeftSourceKeyStream.filterMap_candidates_eq_occurrencePairShiftScan
    (drawingGridSize graph) descriptors selfIndexed commonPeriod localShapes]
  exact occurrencePairCanonicalLeftSourceKeyShiftScanDedupAtPeriod_eq_canonicalized
    wellFormed degree isLocal descriptors occurrencesEq

/-- The guarded selected source stream is exactly the established canonical
crossing compact-word source stream. -/
theorem guardedWords_eq_canonicalCrossingWords
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    (descriptors : List RouteDescriptor)
    (selfIndexed : RouteDescriptorList.SelfIndexed descriptors)
    (commonPeriod :
      ∀ descriptor ∈ descriptors,
        descriptor.gridSize = drawingGridSize graph)
    (localShapes :
      ∀ descriptor ∈ descriptors,
        RouteDescriptorPairAffine.RouteDescriptor.HasLocalShape descriptor)
    (occurrencesEq :
      routeDescriptorNeighborOccurrences descriptors =
        neighborOccurrences graph) :
    guardedWords descriptors =
      CanonicalCrossingCompactAtomWordSources.wordsAtPeriod
        (drawingGridSize graph) descriptors := by
  unfold guardedWords CanonicalCrossingCompactAtomWordSources.wordsAtPeriod
    CanonicalCrossingCompactAtomWordSources.crossingsAtPeriod
  rw [values_eq_canonicalizedCrossingPairs wellFormed degree isLocal
    descriptors selfIndexed commonPeriod localShapes occurrencesEq]
  rw [List.map_map]
  rfl

end CanonicalCrossingShiftLeftSourceKeyRepresentatives
end LeanTrominoes.PeriodicOrthocrossing
