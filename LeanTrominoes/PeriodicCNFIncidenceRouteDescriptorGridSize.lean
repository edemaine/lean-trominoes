/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceMetadataSize
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorCrossingPairs

/-! # Recovering a CNF drawing period from its route descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing

/-- Any nonempty numeric incidence-descriptor stream repeats enough header
data in its first record to recover the exact orthocrossing drawing period. -/
theorem routeDescriptorStreamGridSize_numericRouteDescriptors
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (nonempty : incidencesWithMetadata formula ≠ []) :
    routeDescriptorStreamGridSize (numericRouteDescriptors formula) =
      drawingGridSize formula.incidenceGraph := by
  unfold numericRouteDescriptors
  cases entries : incidencesWithMetadata formula with
  | nil => exact (nonempty entries).elim
  | cons incidence rest =>
      have metadataLength := incidencesWithMetadata_length formula
      rw [entries] at metadataLength
      simp only [List.length_cons] at metadataLength
      simp [entries, routeDescriptorStreamGridSize,
        RouteDescriptor.gridSize, CNFIncidence.numericRouteDescriptor,
        drawingGridSize, metadataLength]

/-- On a nonempty CNF incidence stream, the formula-independent descriptor
scan recovers the exact numeric crossing-pair list. -/
theorem numericOrientedCrossingOccurrencePairs_eq_routeDescriptorStream
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (nonempty : incidencesWithMetadata formula ≠ []) :
    numericOrientedCrossingOccurrencePairs formula =
      routeDescriptorOrientedCrossingOccurrencePairs
        (numericRouteDescriptors formula) := by
  rw [numericOrientedCrossingOccurrencePairs_eq_routeDescriptors]
  unfold routeDescriptorOrientedCrossingOccurrencePairs
  rw [routeDescriptorStreamGridSize_numericRouteDescriptors formula nonempty]

/-- The same factorization at the level required by the marker emitter. -/
theorem numericOrientedCrossingOccurrencePairs_length_eq_routeDescriptorCount
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (nonempty : incidencesWithMetadata formula ≠ []) :
    (numericOrientedCrossingOccurrencePairs formula).length =
      routeDescriptorOrientedCrossingCount
        (numericRouteDescriptors formula) := by
  rw [numericOrientedCrossingOccurrencePairs_eq_routeDescriptorStream
    formula nonempty]
  rfl

end PeriodicCNF
end LeanTrominoes
