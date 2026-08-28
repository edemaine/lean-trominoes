/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorCanonicalCrossingFacts
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorLocalShape
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorSelfIndex
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingRepresentativeCompactAtomWordStreamSemantics

/-! # Canonical crossover words from numeric CNF route descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing

/-- The generic numeric incidence-route descriptor list satisfies every
structural invariant needed by the canonical crossover-word compiler. -/
theorem numericRouteDescriptors_canonicalCrossoverExpandedWords
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal) :
    CanonicalCrossingRepresentativeCompactAtomWordStream.emittedTokens
        (numericRouteDescriptors formula) =
      DelimitedBinaryWords.encode
        ⟨CanonicalCrossingCompactAtomWordSources.expandedWordsAtPeriod
          (drawingGridSize formula.incidenceGraph)
          (numericRouteDescriptors formula)⟩ := by
  exact
    CanonicalCrossingRepresentativeCompactAtomWordStream.emittedTokens_eq_expandedWordsAtPeriod
      wellFormed degree isLocal
      (numericRouteDescriptors formula)
      (numericRouteDescriptors_selfIndexed formula)
      (numericRouteDescriptors_commonDrawingGridSize formula)
      (numericRouteDescriptors_all_hasLocalShape formula forward)
      (routeDescriptorNeighborOccurrences_numericRouteDescriptors formula)

end PeriodicCNF
end LeanTrominoes
