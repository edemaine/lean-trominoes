/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingRepresentativeCompactAtomWordStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyRepresentativeWordStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingCompactAtomWordExpandedSemantics

/-! # Semantics of representative canonical crossover compact atom words -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingRepresentativeCompactAtomWordStream

/-- The compiled stream is the fixed Figure 8(b) expansion of every unique
stable source-pair representative. -/
theorem emittedTokens_eq_representativeExpandedWords
    (descriptors : List RouteDescriptor) :
    emittedTokens descriptors =
      DelimitedBinaryWords.encode
        ⟨CrossoverCompactAtomWords.words
          (CanonicalCrossingShiftLeftSourceKeyRepresentatives.guardedWords
            descriptors)⟩ := by
  unfold emittedTokens
  rw [CanonicalCrossingShiftLeftSourceKeyRepresentativeWordStream.emittedTokens_eq_guardedWords]
  rw [CrossoverCompactAtomWords.tokens_encode]
  rfl

/-- Under the route-descriptor invariants, the compiler emits the exact
canonical crossing expansion in canonical-halo order. -/
theorem emittedTokens_eq_expandedWordsAtPeriod
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
        ⟨CanonicalCrossingCompactAtomWordSources.expandedWordsAtPeriod
          (drawingGridSize graph) descriptors⟩ := by
  rw [emittedTokens_eq_representativeExpandedWords]
  rw [CanonicalCrossingShiftLeftSourceKeyRepresentatives.guardedWords_eq_canonicalCrossingWords
    wellFormed degree isLocal descriptors selfIndexed commonPeriod
    localShapes occurrencesEq]
  rfl

/-- Equivalently, the output is exactly the clause-major Figure 8(b) compact
atom-word block attached to each canonical crossing. -/
theorem emittedTokens_eq_canonicalCrossoverBlocks
    {Vertex Variable : Type*} [DecidableEq Vertex]
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
        neighborOccurrences graph)
    (sourceWord : Variable → List Bool) :
    emittedTokens descriptors =
      DelimitedBinaryWords.encode
        ⟨(canonicalizedCrossingHalo graph).flatMap fun crossing =>
          PlanarThreeSAT.crossoverFormula.flatMap fun clause =>
            clause.literals.map fun literal =>
              RetainedCompactAtomWords.word sourceWord
                ⟨normalizedCrossoverAtom crossing literal.1⟩⟩ := by
  rw [emittedTokens_eq_expandedWordsAtPeriod wellFormed degree isLocal
    descriptors selfIndexed commonPeriod localShapes occurrencesEq]
  rw [CanonicalCrossingCompactAtomWordSources.expandedWordsAtPeriod_eq
    graph descriptors occurrencesEq sourceWord]

end CanonicalCrossingRepresentativeCompactAtomWordStream
end LeanTrominoes.PeriodicOrthocrossing
