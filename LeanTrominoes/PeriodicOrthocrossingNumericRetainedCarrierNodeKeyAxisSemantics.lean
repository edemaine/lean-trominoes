/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceCrossingOccurrencePairEnumeration
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorGridSize
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierNodeSemantics
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierNodeKeyAxisSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorRetainedCarrierBitData

/-! # Key-derived axes of numeric route-descriptor carrier nodes -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Every node in the retained stream reconstructed from numeric CNF route
descriptors receives its physical horizontal bit from the carrier-key axis
datum. -/
theorem numericRetainedCarrierNode_carrierKey_axisValue
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ [])
    {node : CarrierNode}
    (nodeMember : node ∈ routeDescriptorRetainedCarrierNodesAtPeriod
      (routeDescriptorStreamGridSize
        (PeriodicCNF.numericRouteDescriptors formula))
      (PeriodicCNF.numericRouteDescriptors formula)) :
    RouteDescriptorCarrierKeyAxisDatum.value
        (PeriodicCNF.numericRouteDescriptors formula)
        (some node.carrierKey) =
      FixedAxisUnaryFields.value true node.isHorizontal := by
  apply retainedCarrierNode_carrierKey_axisValue
    formula.incidenceGraph
    (PeriodicCNF.numericRouteDescriptors formula)
  · rw [PeriodicCNF.incidenceGraph_indexedSegments_eq_numeric,
      PeriodicCNF.numericIndexedSegments_eq_routeDescriptorIndexedSegments]
  · rw [retainedDrawingCarrierNodes_eq_occurrencesAndPairs]
    unfold routeDescriptorRetainedCarrierNodesAtPeriod at nodeMember
    rw [PeriodicCNF.routeDescriptorStreamGridSize_numericRouteDescriptors
      formula nonempty] at nodeMember
    rw [PeriodicCNF.incidenceGraph_neighborOccurrences_eq_numeric,
      PeriodicCNF.numericNeighborOccurrences_eq_routeDescriptorNeighborOccurrences,
      PeriodicCNF.incidenceGraph_orientedCrossingOccurrencePairs_eq_numeric,
      PeriodicCNF.numericOrientedCrossingOccurrencePairs_eq_routeDescriptors]
    exact nodeMember

end LeanTrominoes.PeriodicOrthocrossing
