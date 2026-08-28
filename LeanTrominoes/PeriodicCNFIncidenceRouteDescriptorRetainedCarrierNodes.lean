/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorCrossingPairs
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorGridSize
import LeanTrominoes.PeriodicCNFIncidenceCrossingOccurrencePairEnumeration
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierNodeSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorRetainedCarrierBitData

/-! # Retained carrier nodes reconstructed from numeric route descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing

/-- At the semantic drawing period, the graph-free numeric-descriptor scan
reconstructs the retained carrier-node presentation exactly. -/
theorem routeDescriptorRetainedCarrierNodes_numeric_eq
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    routeDescriptorRetainedCarrierNodesAtPeriod
        (drawingGridSize formula.incidenceGraph)
        (numericRouteDescriptors formula) =
      retainedDrawingCarrierNodes formula.incidenceGraph := by
  rw [retainedDrawingCarrierNodes_eq_occurrencesAndPairs]
  unfold routeDescriptorRetainedCarrierNodesAtPeriod
  rw [incidenceGraph_neighborOccurrences_eq_numeric,
    numericNeighborOccurrences_eq_routeDescriptorNeighborOccurrences,
    incidenceGraph_orientedCrossingOccurrencePairs_eq_numeric,
    numericOrientedCrossingOccurrencePairs_eq_routeDescriptors]

end PeriodicCNF
end LeanTrominoes
