/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorGridSize
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRetainedPairPhysicalSemantics
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierNodeSemantics
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierOrderSemantics
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierLensGeometry

/-! # Geometric span bounds for selected global carrier-rank pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

private theorem routeDescriptorRetainedCarrierNodes_numeric_eq
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    routeDescriptorRetainedCarrierNodesAtPeriod
        (drawingGridSize formula.incidenceGraph)
        (PeriodicCNF.numericRouteDescriptors formula) =
      retainedDrawingCarrierNodes formula.incidenceGraph := by
  rw [retainedDrawingCarrierNodes_eq_occurrencesAndPairs]
  unfold routeDescriptorRetainedCarrierNodesAtPeriod
  rw [PeriodicCNF.incidenceGraph_neighborOccurrences_eq_numeric,
    PeriodicCNF.numericNeighborOccurrences_eq_routeDescriptorNeighborOccurrences,
    PeriodicCNF.incidenceGraph_orientedCrossingOccurrencePairs_eq_numeric,
    PeriodicCNF.numericOrientedCrossingOccurrencePairs_eq_routeDescriptors]

/-- Every selected rank-matrix pair from valid numeric routes has at least
the ten-cell physical carrier separation, hence exceeds the decoder's
six-cell span threshold. -/
theorem retainedPredicate_spanLarge_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    let descriptors := PeriodicCNF.numericRouteDescriptors formula
    let period := routeDescriptorStreamGridSize descriptors
    let nodes :=
      routeDescriptorRetainedCarrierNodesAtPeriod period descriptors
    let datums :=
      (nodes.map (carrierNodeRankDatumAtPeriod period)).dedup
    let entries := CarrierRankGlobal.enumeration datums
    ∀ first ∈ entries.zipIdx, ∀ second ∈ entries.zipIdx,
      retainedPredicate first second = true →
        6 < (second.1.1.orderCoordinate -
          first.1.1.orderCoordinate).toNat := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let period := routeDescriptorStreamGridSize descriptors
  let nodes :=
    routeDescriptorRetainedCarrierNodesAtPeriod period descriptors
  let datums :=
    (nodes.map (carrierNodeRankDatumAtPeriod period)).dedup
  let entries := CarrierRankGlobal.enumeration datums
  change ∀ first ∈ entries.zipIdx, ∀ second ∈ entries.zipIdx,
    retainedPredicate first second = true →
      6 < (second.1.1.orderCoordinate -
        first.1.1.orderCoordinate).toNat
  intro first firstMember second secondMember retained
  have periodEq : period = drawingGridSize formula.incidenceGraph := by
    simpa [period, descriptors] using
      PeriodicCNF.routeDescriptorStreamGridSize_numericRouteDescriptors
        formula nonempty
  have nodesEq :
      nodes = retainedDrawingCarrierNodes formula.incidenceGraph := by
    unfold nodes
    rw [periodEq]
    exact routeDescriptorRetainedCarrierNodes_numeric_eq formula
  rcases retainedPredicate_exists_physicalPair period nodes
      first second firstMember secondMember retained with
    ⟨pair, pairMember, firstDatumEq, secondDatumEq⟩
  rw [IndexedConsecutivePairs.pairs_eq_consecutivePairs] at pairMember
  have semanticPairMember :
      pair ∈ consecutivePairs
        (retainedCompleteCarrierNodes formula.incidenceGraph
          first.1.1.key) := by
    rw [retainedCompleteCarrierNodes_eq_atPeriod]
    simpa [periodEq, nodesEq] using pairMember
  have separated := retainedCompleteCarrierPair_orderCoordinate_add_ten_le
    wellFormed degree isLocal first.1.1.key semanticPairMember
  have firstOrderEq :
      first.1.1.orderCoordinate =
        pair.1.orderCoordinate formula.incidenceGraph := by
    calc
      first.1.1.orderCoordinate =
          (carrierNodeRankDatumAtPeriod period pair.1).orderCoordinate :=
        (congrArg CarrierNodeRankDatum.orderCoordinate firstDatumEq).symm
      _ = carrierNodeOrderCoordinateAtPeriod period pair.1 := rfl
      _ = pair.1.orderCoordinate formula.incidenceGraph := by
        simpa [periodEq] using
          carrierNodeOrderCoordinateAtPeriod_drawingGridSize
            formula.incidenceGraph pair.1
  have secondOrderEq :
      second.1.1.orderCoordinate =
        pair.2.orderCoordinate formula.incidenceGraph := by
    calc
      second.1.1.orderCoordinate =
          (carrierNodeRankDatumAtPeriod period pair.2).orderCoordinate :=
        (congrArg CarrierNodeRankDatum.orderCoordinate secondDatumEq).symm
      _ = carrierNodeOrderCoordinateAtPeriod period pair.2 := rfl
      _ = pair.2.orderCoordinate formula.incidenceGraph := by
        simpa [periodEq] using
          carrierNodeOrderCoordinateAtPeriod_drawingGridSize
            formula.incidenceGraph pair.2
  rw [firstOrderEq, secondOrderEq]
  omega

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
