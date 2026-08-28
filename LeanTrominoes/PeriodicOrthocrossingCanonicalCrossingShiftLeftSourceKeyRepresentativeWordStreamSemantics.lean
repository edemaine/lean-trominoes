/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyRepresentativeWordStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyRepresentativeFieldLookupSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierSourcePairFieldFormatterStreamSemantics

/-! # Semantics of representative canonical crossing source-pair words -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingShiftLeftSourceKeyRepresentativeWordStream

/-- The representative-field compiler reconstructs exactly one guarded word
for each stable source-pair representative. -/
theorem emittedTokens_eq_guardedWords (descriptors : List RouteDescriptor) :
    emittedTokens descriptors =
      DelimitedBinaryWords.encode
        ⟨CanonicalCrossingShiftLeftSourceKeyRepresentatives.guardedWords
          descriptors⟩ := by
  unfold emittedTokens
  rw [CanonicalCrossingShiftLeftSourceKeyRepresentativeFieldLookup.selectedFields_eq_semanticFields]
  unfold CanonicalCrossingShiftLeftSourceKeyRepresentativeFieldLookup.semanticFields
  rw [CarrierSourcePairFieldFormatter.output_sourcePairs]
  rfl

/-- Under the route-descriptor invariants, the reconstructed word stream is
the exact canonical crossing source stream. -/
theorem emittedTokens_eq_canonicalCrossingWords
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
    emittedTokens descriptors =
      DelimitedBinaryWords.encode
        ⟨CanonicalCrossingCompactAtomWordSources.wordsAtPeriod
          (drawingGridSize graph) descriptors⟩ := by
  rw [emittedTokens_eq_guardedWords]
  rw [CanonicalCrossingShiftLeftSourceKeyRepresentatives.guardedWords_eq_canonicalCrossingWords
    wellFormed degree isLocal descriptors selfIndexed commonPeriod
    localShapes occurrencesEq]

end CanonicalCrossingShiftLeftSourceKeyRepresentativeWordStream
end LeanTrominoes.PeriodicOrthocrossing
