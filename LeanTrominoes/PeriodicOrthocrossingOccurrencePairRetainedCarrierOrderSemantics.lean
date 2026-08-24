/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierOrderData
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNodePositionSemantics
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierNodeSemantics

/-! # Semantics of graph-free retained carrier ordering -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Sorting the semantic retained node stream at the graph's numeric period
reproduces the semantic complete carrier chain exactly. -/
theorem retainedCompleteCarrierNodes_eq_atPeriod
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (key : Nat × Nat × Cell) :
    retainedCompleteCarrierNodes graph key =
      retainedCompleteCarrierNodesAtPeriod
        (drawingGridSize graph)
        (retainedDrawingCarrierNodes graph) key := by
  unfold retainedCompleteCarrierNodes
    retainedCompleteCarrierNodesAtPeriod
  simp_rw [carrierNodeOrderCoordinateAtPeriod_drawingGridSize]

/-- Substituting the occurrence-pair event stream preserves the exact sorted
carrier chain. -/
theorem retainedCompleteCarrierNodes_eq_occurrencesAndPairsAtPeriod
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (key : Nat × Nat × Cell) :
    retainedCompleteCarrierNodes graph key =
      retainedCompleteCarrierNodesAtPeriod
        (drawingGridSize graph)
        (retainedCarrierNodesOfOccurrencesAndPairsAtPeriod
          (drawingGridSize graph)
          (neighborOccurrences graph)
          (orientedCrossingOccurrencePairs graph)) key := by
  rw [retainedCompleteCarrierNodes_eq_atPeriod,
    retainedDrawingCarrierNodes_eq_occurrencesAndPairs]

/-- The data-level adjacent node-pair scan has exactly the endpoint order of
the semantic retained complete-carrier links. -/
theorem retainedCompleteCarrierLinks_eq_nodePairsAtPeriod
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (key : Nat × Nat × Cell) :
    retainedCompleteCarrierLinks graph key =
      (retainedCompleteCarrierNodePairsAtPeriod
        (drawingGridSize graph)
        (retainedCarrierNodesOfOccurrencesAndPairsAtPeriod
          (drawingGridSize graph)
          (neighborOccurrences graph)
          (orientedCrossingOccurrencePairs graph)) key).map
        (carrierNodePairLink graph) := by
  unfold retainedCompleteCarrierLinks
    retainedCompleteCarrierNodePairsAtPeriod
  rw [← retainedCompleteCarrierNodes_eq_occurrencesAndPairsAtPeriod]

end LeanTrominoes.PeriodicOrthocrossing
