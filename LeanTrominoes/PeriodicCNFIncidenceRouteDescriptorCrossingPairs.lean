/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceCrossingOccurrencePairEnumerationData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCrossingPairData

/-! # CNF crossing scans factor through numeric route descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing

/-- The numeric indexed-segment stream depends only on the compact route
descriptor list. -/
theorem numericIndexedSegments_eq_routeDescriptorIndexedSegments
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    numericIndexedSegments formula =
      routeDescriptorIndexedSegments (numericRouteDescriptors formula) := by
  rfl

/-- The neighboring occurrence stream likewise factors through the compact
route descriptors. -/
theorem numericNeighborOccurrences_eq_routeDescriptorNeighborOccurrences
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    numericNeighborOccurrences formula =
      routeDescriptorNeighborOccurrences
        (numericRouteDescriptors formula) := by
  rfl

/-- The complete graph-free crossing scan is exactly the generic descriptor
postprocessor at the incidence drawing's numeric period. -/
theorem numericOrientedCrossingOccurrencePairs_eq_routeDescriptors
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    numericOrientedCrossingOccurrencePairs formula =
      routeDescriptorOrientedCrossingOccurrencePairsAtPeriod
        (drawingGridSize formula.incidenceGraph)
        (numericRouteDescriptors formula) := by
  rfl

/-- The numeric crossing count can therefore be computed without retaining
the source formula once its period and route descriptors have been emitted. -/
theorem numericOrientedCrossingOccurrencePairs_length_eq_descriptorCount
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (numericOrientedCrossingOccurrencePairs formula).length =
      routeDescriptorOrientedCrossingCountAtPeriod
        (drawingGridSize formula.incidenceGraph)
        (numericRouteDescriptors formula) := by
  rfl

end PeriodicCNF
end LeanTrominoes
