/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierRepresentativeData
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierOrderSemantics
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierRepresentativeKeyData

/-! # Semantics of graph-free representative retained carrier pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The numeric crossing quotient agrees with graph-based normalization at
the graph's drawing period. -/
theorem crossingRecordPeriodShiftAtPeriod_drawingGridSize
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (record : CrossingRecord) :
    crossingRecordPeriodShiftAtPeriod
        (drawingGridSize graph) record =
      crossingPeriodShift graph record := by
  rfl

/-- Pair ownership computed from numeric data agrees with ownership of the
positioned semantic link having those endpoints. -/
theorem carrierNodePairRepresentativeShiftAtPeriod_drawingGridSize
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (pair : CarrierNode × CarrierNode) :
    carrierNodePairRepresentativeShiftAtPeriod
        (drawingGridSize graph) pair =
      carrierLinkRepresentativeShift graph
        (carrierNodePairLink graph pair) := by
  rcases pair with ⟨first, second⟩
  cases first <;> cases second <;> rfl

/-- The graph-free and semantic zero-owner predicates coincide pointwise. -/
theorem carrierNodePairIsRepresentativeAtPeriod_iff
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (pair : CarrierNode × CarrierNode) :
    CarrierNodePairIsRepresentativeAtPeriod
        (drawingGridSize graph) pair ↔
      CarrierLinkIsRepresentative graph
        (carrierNodePairLink graph pair) := by
  unfold CarrierNodePairIsRepresentativeAtPeriod
    CarrierLinkIsRepresentative
  rw [carrierNodePairRepresentativeShiftAtPeriod_drawingGridSize]

/-- Filtering the reconstructed adjacent pairs by numeric ownership gives
exactly the semantic representative-link block, in the same order. -/
theorem retainedRepresentativeCarrierLinksAt_eq_nodePairsAtPeriod
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (key : Nat × Nat × Cell) :
    retainedRepresentativeCarrierLinksAt graph key =
      (retainedRepresentativeCarrierNodePairsAtPeriod
        (drawingGridSize graph)
        (retainedCarrierNodesOfOccurrencesAndPairsAtPeriod
          (drawingGridSize graph)
          (neighborOccurrences graph)
          (orientedCrossingOccurrencePairs graph)) key).map
        (carrierNodePairLink graph) := by
  unfold retainedRepresentativeCarrierLinksAt
    retainedRepresentativeCarrierNodePairsAtPeriod
  rw [retainedCompleteCarrierLinks_eq_nodePairsAtPeriod,
    List.filter_map]
  congr 1

end LeanTrominoes.PeriodicOrthocrossing
