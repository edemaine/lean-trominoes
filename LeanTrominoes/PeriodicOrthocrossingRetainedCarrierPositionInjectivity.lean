/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingPlanarSATVertexPositionGeometry
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierBendProximity

/-!
# Injective positions of retained carrier nodes

The refined position of a carrier node records a drawing-grid center and one
of four directional local ports.  Equal refined positions therefore force
the same center and direction.  The supporting source segments overlap
continuously in that direction, so continuous lane uniqueness identifies the
carrier occurrence; strict order on that occurrence then identifies the node.
-/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- Terminals at one drawing point with the same local port extend into
overlapping relative segment interiors. -/
theorem
    segmentTerminal_supportingSegments_interiorsMeet_of_drawingPoint_eq_of_localPosition_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (first second : SegmentTerminal)
    (firstAligned : first.indexed.segment.IsAxisAligned)
    (secondAligned : second.indexed.segment.IsAxisAligned)
    (pointEq :
      first.drawingPoint graph = second.drawingPoint graph)
    (localEq :
      segmentTerminalLocalPosition
          first.indexed.segment first.endpoint =
        segmentTerminalLocalPosition
          second.indexed.segment second.endpoint) :
    (first.indexed.segment.translate
        ((drawing graph).periodTranslation first.translate)).InteriorsMeet
      (second.indexed.segment.translate
        ((drawing graph).periodTranslation second.translate)) := by
  rcases first with
    ⟨⟨firstRoute, firstIndex,
      ⟨⟨firstStartX, firstStartY⟩,
        ⟨firstFinishX, firstFinishY⟩⟩⟩,
      firstTranslate, firstEndpoint⟩
  rcases second with
    ⟨⟨secondRoute, secondIndex,
      ⟨⟨secondStartX, secondStartY⟩,
        ⟨secondFinishX, secondFinishY⟩⟩⟩,
      secondTranslate, secondEndpoint⟩
  rcases firstAligned with firstHorizontal | firstVertical
  · rcases secondAligned with secondHorizontal | secondVertical
    · rcases firstHorizontal with
        ⟨firstYEq, firstXNe⟩
      rcases secondHorizontal with
        ⟨secondYEq, secondXNe⟩
      cases firstEndpoint <;> cases secondEndpoint <;>
        simp [SegmentTerminal.drawingPoint,
          segmentTerminalLocalPosition,
          GridSegment.InteriorsMeet,
          GridSegment.IsHorizontal, GridSegment.IsVertical,
          GridSegment.OpenIntervalsOverlap,
          GridSegment.translate,
          PeriodicGridDrawing.periodTranslation,
          Cell.add, Cell.scale] at pointEq localEq ⊢ <;>
        split_ifs at localEq <;>
        simp_all <;> omega
    · rcases firstHorizontal with
        ⟨firstYEq, firstXNe⟩
      rcases secondVertical with
        ⟨secondXEq, secondYNe⟩
      cases firstEndpoint <;> cases secondEndpoint <;>
        simp [segmentTerminalLocalPosition] at localEq <;>
        split_ifs at localEq <;> simp_all <;> omega
  · rcases secondAligned with secondHorizontal | secondVertical
    · rcases firstVertical with
        ⟨firstXEq, firstYNe⟩
      rcases secondHorizontal with
        ⟨secondYEq, secondXNe⟩
      cases firstEndpoint <;> cases secondEndpoint <;>
        simp [segmentTerminalLocalPosition] at localEq <;>
        split_ifs at localEq <;> simp_all <;> omega
    · rcases firstVertical with
        ⟨firstXEq, firstYNe⟩
      rcases secondVertical with
        ⟨secondXEq, secondYNe⟩
      cases firstEndpoint <;> cases secondEndpoint <;>
        simp [SegmentTerminal.drawingPoint,
          segmentTerminalLocalPosition,
          GridSegment.InteriorsMeet,
          GridSegment.IsHorizontal, GridSegment.IsVertical,
          GridSegment.OpenIntervalsOverlap,
          GridSegment.translate,
          PeriodicGridDrawing.periodTranslation,
          Cell.add, Cell.scale] at pointEq localEq ⊢ <;>
        split_ifs at localEq <;>
        simp_all <;> omega

/-- Equal genuine carrier ports belong to the same horizontal or vertical
axis family. -/
theorem retainedCarrierNode_isHorizontal_eq_of_localPosition_eq
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {first second : CarrierNode}
    (firstMem : first ∈ retainedDrawingCarrierNodes graph)
    (secondMem : second ∈ retainedDrawingCarrierNodes graph)
    (firstAligned : first.indexed.segment.IsAxisAligned)
    (secondAligned : second.indexed.segment.IsAxisAligned)
    (localEq : first.localPosition = second.localPosition) :
    first.isHorizontal = second.isHorizontal := by
  have firstData :=
    retainedCarrierNode_localPosition_axis_data
      graph firstMem firstAligned
  have secondData :=
    retainedCarrierNode_localPosition_axis_data
      graph secondMem secondAligned
  by_cases firstHorizontal : first.isHorizontal = true
  · by_cases secondHorizontal : second.isHorizontal = true
    · exact firstHorizontal.trans secondHorizontal.symm
    · have secondVertical : second.isHorizontal = false :=
        Bool.eq_false_iff.mpr secondHorizontal
      rw [if_pos firstHorizontal] at firstData
      rw [if_neg secondHorizontal] at secondData
      rw [localEq] at firstData
      have impossible :
          (6 : Int) % 10 = 1 := by
        rw [← secondData.1]
        exact firstData.2
      norm_num at impossible
  · have firstVertical : first.isHorizontal = false :=
      Bool.eq_false_iff.mpr firstHorizontal
    by_cases secondHorizontal : second.isHorizontal = true
    · rw [if_neg firstHorizontal] at firstData
      rw [if_pos secondHorizontal] at secondData
      rw [localEq] at firstData
      have impossible :
          (6 : Int) % 10 = 1 := by
        rw [← secondData.1]
        exact firstData.2
      norm_num at impossible
    · have secondVertical : second.isHorizontal = false :=
        Bool.eq_false_iff.mpr secondHorizontal
      exact firstVertical.trans secondVertical.symm

/-- The refined physical position is injective on the retained carrier-node
enumeration. -/
theorem retainedCarrierNode_eq_of_position_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {first second : CarrierNode}
    (firstMem : first ∈ retainedDrawingCarrierNodes graph)
    (secondMem : second ∈ retainedDrawingCarrierNodes graph)
    (positionEq : first.position graph = second.position graph) :
    first = second := by
  have positionData :=
    planarSATMacrocellPosition_eq
      (CarrierNode.localPosition_in_macrocell first)
      (CarrierNode.localPosition_in_macrocell second)
      (by
        rw [← CarrierNode.position_eq_scale_add_local graph first,
          ← CarrierNode.position_eq_scale_add_local graph second]
        exact positionEq)
  have pointEq : first.drawingPoint graph =
      second.drawingPoint graph := positionData.1
  have localEq : first.localPosition =
      second.localPosition := positionData.2
  have firstIndexedMem :
      first.indexed ∈ (drawing graph).indexedSegments :=
    retainedCarrierNode_indexed_mem graph firstMem
  have secondIndexedMem :
      second.indexed ∈ (drawing graph).indexedSegments :=
    retainedCarrierNode_indexed_mem graph secondMem
  have firstAligned :
      first.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      first.indexed firstIndexedMem
  have secondAligned :
      second.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      second.indexed secondIndexedMem
  have horizontalEq :
      first.isHorizontal = second.isHorizontal :=
    retainedCarrierNode_isHorizontal_eq_of_localPosition_eq
      graph firstMem secondMem
      firstAligned secondAligned localEq
  have firstSupportAligned :
      (first.supportingSegment graph).IsAxisAligned := by
    exact (GridSegment.isAxisAligned_translate _ _).mpr firstAligned
  have secondSupportAligned :
      (second.supportingSegment graph).IsAxisAligned := by
    exact (GridSegment.isAxisAligned_translate _ _).mpr secondAligned
  have parallel :
      ((first.supportingSegment graph).IsHorizontal ∧
          (second.supportingSegment graph).IsHorizontal) ∨
        ((first.supportingSegment graph).IsVertical ∧
          (second.supportingSegment graph).IsVertical) := by
    by_cases firstHorizontal : first.isHorizontal = true
    · have firstHorizontalSegment :
          first.indexed.segment.IsHorizontal :=
        (retainedCarrierNode_isHorizontal_iff
          graph firstMem firstAligned).mp firstHorizontal
      have secondHorizontalTag :
          second.isHorizontal = true := by
        rw [← horizontalEq]
        exact firstHorizontal
      have secondHorizontalSegment :
          second.indexed.segment.IsHorizontal :=
        (retainedCarrierNode_isHorizontal_iff
          graph secondMem secondAligned).mp secondHorizontalTag
      exact Or.inl
        ⟨(GridSegment.isHorizontal_translate _ _).mpr
            firstHorizontalSegment,
          (GridSegment.isHorizontal_translate _ _).mpr
            secondHorizontalSegment⟩
    · have firstVerticalSegment :
          first.indexed.segment.IsVertical := by
        apply firstAligned.resolve_left
        intro horizontal
        exact firstHorizontal
          ((retainedCarrierNode_isHorizontal_iff
            graph firstMem firstAligned).mpr horizontal)
      have secondHorizontalFalse :
          second.isHorizontal ≠ true := by
        rw [← horizontalEq]
        exact firstHorizontal
      have secondVerticalSegment :
          second.indexed.segment.IsVertical := by
        apply secondAligned.resolve_left
        intro horizontal
        exact secondHorizontalFalse
          ((retainedCarrierNode_isHorizontal_iff
            graph secondMem secondAligned).mpr horizontal)
      exact Or.inr
        ⟨(GridSegment.isVertical_translate _ _).mpr
            firstVerticalSegment,
          (GridSegment.isVertical_translate _ _).mpr
            secondVerticalSegment⟩
  have interiorsMeet :
      (first.supportingSegment graph).InteriorsMeet
        (second.supportingSegment graph) := by
    cases first with
    | boundary firstBoundary =>
        have firstBoundaryMem :
            firstBoundary ∈ retainedCrossingBoundaries graph := by
          unfold retainedDrawingCarrierNodes at firstMem
          simpa using firstMem
        have firstContains :=
          (retainedCrossingBoundary_indexed_mem_and_contains
            graph firstBoundaryMem).2
        cases second with
        | boundary secondBoundary =>
            have secondBoundaryMem :
                secondBoundary ∈ retainedCrossingBoundaries graph := by
              unfold retainedDrawingCarrierNodes at secondMem
              simpa using secondMem
            apply GridSegment.interiorsMeet_of_interiorContains
              firstContains
            have secondContains :=
              (retainedCrossingBoundary_indexed_mem_and_contains
                graph secondBoundaryMem).2
            change
              firstBoundary.crossing.point =
                secondBoundary.crossing.point at pointEq
            rw [← pointEq] at secondContains
            change
              (secondBoundary.indexed.segment.translate
                ((drawing graph).periodTranslation
                  secondBoundary.translate)).InteriorContains
                firstBoundary.crossing.point
            exact secondContains
        | terminal secondTerminal =>
            apply
              GridSegment.interiorsMeet_of_interiorContains_endpoint
                firstContains parallel
            have terminalEndpoint :
                secondTerminal.drawingPoint graph =
                    ((CarrierNode.terminal secondTerminal)
                      |>.supportingSegment graph).start ∨
                  secondTerminal.drawingPoint graph =
                    ((CarrierNode.terminal secondTerminal)
                      |>.supportingSegment graph).finish := by
              rcases secondTerminal with
                ⟨indexed, translate, endpoint⟩
              cases endpoint <;>
                simp [SegmentTerminal.drawingPoint,
                  CarrierNode.supportingSegment,
                  CarrierNode.indexed, CarrierNode.translate]
            change
              firstBoundary.crossing.point =
                secondTerminal.drawingPoint graph at pointEq
            exact terminalEndpoint.imp
              (pointEq.trans ·) (pointEq.trans ·)
    | terminal firstTerminal =>
        have firstTerminalMem :
            firstTerminal ∈ drawingSegmentTerminals graph := by
          unfold retainedDrawingCarrierNodes at firstMem
          simpa using firstMem
        cases second with
        | boundary secondBoundary =>
            have secondBoundaryMem :
                secondBoundary ∈ retainedCrossingBoundaries graph := by
              unfold retainedDrawingCarrierNodes at secondMem
              simpa using secondMem
            apply (GridSegment.interiorsMeet_comm _ _).mpr
            apply
              GridSegment.interiorsMeet_of_interiorContains_endpoint
                (retainedCrossingBoundary_indexed_mem_and_contains
                  graph secondBoundaryMem).2
                (by
                  rcases parallel with horizontal | vertical
                  · exact Or.inl ⟨horizontal.2, horizontal.1⟩
                  · exact Or.inr ⟨vertical.2, vertical.1⟩)
            have terminalEndpoint :
                firstTerminal.drawingPoint graph =
                    ((CarrierNode.terminal firstTerminal)
                      |>.supportingSegment graph).start ∨
                  firstTerminal.drawingPoint graph =
                    ((CarrierNode.terminal firstTerminal)
                      |>.supportingSegment graph).finish := by
              rcases firstTerminal with
                ⟨indexed, translate, endpoint⟩
              cases endpoint <;>
                simp [SegmentTerminal.drawingPoint,
                  CarrierNode.supportingSegment,
                  CarrierNode.indexed, CarrierNode.translate]
            change
              firstTerminal.drawingPoint graph =
                secondBoundary.crossing.point at pointEq
            exact terminalEndpoint.imp
              ((pointEq.symm.trans ·)) ((pointEq.symm.trans ·))
        | terminal secondTerminal =>
            exact
              segmentTerminal_supportingSegments_interiorsMeet_of_drawingPoint_eq_of_localPosition_eq
              graph firstTerminal secondTerminal
              firstAligned secondAligned pointEq localEq
  have keyEq : first.carrierKey = second.carrierKey := by
    rcases parallel with horizontal | vertical
    · have keyData :=
        drawing_hasUniqueHorizontalContinuousInteriors
          wellFormed degree isLocal
          first.indexed firstIndexedMem
          second.indexed secondIndexedMem
          first.translate second.translate
          horizontal.1 horizontal.2 interiorsMeet
      simpa [CarrierNode.carrierKey_eq_indexed_translate] using keyData
    · have keyData :=
        drawing_hasUniqueVerticalContinuousInteriors
          wellFormed degree isLocal
          first.indexed firstIndexedMem
          second.indexed secondIndexedMem
          first.translate second.translate
          vertical.1 vertical.2 interiorsMeet
      simpa [CarrierNode.carrierKey_eq_indexed_translate] using keyData
  have coordinateEq :
      first.orderCoordinate graph =
        second.orderCoordinate graph := by
    unfold CarrierNode.orderCoordinate
    by_cases horizontal : first.isHorizontal = true
    · rw [if_pos horizontal, if_pos (horizontalEq ▸ horizontal)]
      exact congrArg Prod.fst positionEq
    · rw [if_neg horizontal,
        if_neg (by rwa [← horizontalEq])]
      exact congrArg Prod.snd positionEq
  exact retainedCarrierNode_eq_of_commonCarrier_orderCoordinate_eq
    wellFormed degree isLocal firstMem secondMem keyEq coordinateEq

end LeanTrominoes.PeriodicOrthocrossing
