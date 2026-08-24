/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierNodeData
import LeanTrominoes.PeriodicOrthocrossingRetainedCrossingOccurrencePairOrderSemantics
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierLinks

/-! # Semantics of occurrence-pair retained carrier nodes -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The semantic retained carrier-node list is exactly the graph-free event
stream reconstructed from neighboring occurrences and canonical occurrence
pairs at the graph's drawing period. -/
theorem retainedDrawingCarrierNodes_eq_occurrencesAndPairs
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    retainedDrawingCarrierNodes graph =
      retainedCarrierNodesOfOccurrencesAndPairsAtPeriod
        (drawingGridSize graph)
        (neighborOccurrences graph)
        (orientedCrossingOccurrencePairs graph) := by
  unfold retainedDrawingCarrierNodes
    retainedCarrierNodesOfOccurrencesAndPairsAtPeriod
    occurrenceCarrierTerminalNodes
    crossingRecordCarrierBoundaryNodes
    drawingSegmentTerminals retainedCrossingBoundaries
  rw [retainedCrossings_eq_occurrencePairRecordScan]
  rw [List.map_flatMap, List.map_flatMap]

end LeanTrominoes.PeriodicOrthocrossing
