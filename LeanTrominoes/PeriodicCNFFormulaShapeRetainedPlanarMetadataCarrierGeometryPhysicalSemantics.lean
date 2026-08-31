/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierPairNextSliceSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierFallbackRouteTailRecordGeometryData
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierLensGeometry
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierRepresentativeKeyBlockSemantics
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierRepresentativeSemantics

/-! # Physical retained-carrier geometries as semantic links -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing
open CarrierFallbackRouteTailRecords

/-- Concatenating physical representative-pair geometries over the stable
carrier keys gives exactly one semantic geometry per retained carrier link,
in presentation order. -/
theorem physicalCarrierGeometries_eq_links
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal) :
    (retainedDrawingCompleteCarrierKeys source.incidenceGraph).flatMap
        (fun key =>
          (retainedRepresentativeCarrierNodePairsAtPeriod
            (drawingGridSize source.incidenceGraph)
            (retainedDrawingCarrierNodes source.incidenceGraph) key).map
              (Geometry.ofNodePairAtPeriod
                (drawingGridSize source.incidenceGraph))) =
      (retainedDrawingCompleteCarrierLinks source.incidenceGraph).map
        (Geometry.ofLink source) := by
  rw [retainedDrawingCarrierNodes_eq_occurrencesAndPairs]
  rw [retainedDrawingCompleteCarrierLinks_eq_keyBlocks,
    List.map_flatMap]
  apply List.flatMap_congr
  intro key _keyMember
  rw [retainedRepresentativeCarrierLinksAt_eq_nodePairsAtPeriod]
  rw [List.map_map]
  apply List.map_congr_left
  intro pair pairMember
  have rawPairMember := (List.mem_filter.mp pairMember).1
  have consecutiveMember :
      pair ∈ consecutivePairs (retainedCompleteCarrierNodes
        source.incidenceGraph key) := by
    unfold retainedCompleteCarrierNodePairsAtPeriod at rawPairMember
    have consecutiveAtPeriod := (List.mem_filter.mp rawPairMember).1
    rw [← retainedCompleteCarrierNodes_eq_occurrencesAndPairsAtPeriod]
      at consecutiveAtPeriod
    exact consecutiveAtPeriod
  have members := mem_of_mem_consecutivePairs consecutiveMember
  have firstData :=
    (mem_retainedCompleteCarrierNodes_iff
      source.incidenceGraph key pair.1).mp members.1
  have secondData :=
    (mem_retainedCompleteCarrierNodes_iff
      source.incidenceGraph key pair.2).mp members.2
  have sameAxis : pair.1.isHorizontal = pair.2.isHorizontal :=
    retainedCarrierNode_isHorizontal_eq_of_carrierKey_eq
      wellFormed degree isLocal firstData.1 secondData.1
      (firstData.2.trans secondData.2.symm)
  have clearance := retainedCompleteCarrierPair_hasForwardClearance
    wellFormed degree isLocal key consecutiveMember
  have spanEq :=
    CarrierNode.axisSpan_eq_orderCoordinate_sub_of_hasForwardClearance
      source.incidenceGraph pair.1 pair.2 sameAxis clearance
  unfold Geometry.ofNodePairAtPeriod Geometry.ofLink
  congr 1
  · exact carrierNodePairNextSliceAtPeriod_eq_carrierLinkNextSlice
      source pair
  · simp only [carrierNodePairLink,
      carrierNodeOrderCoordinateAtPeriod_drawingGridSize]
    rw [spanEq]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
