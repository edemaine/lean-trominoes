import LeanTrominoes.PeriodicOrthocrossingCrossoverCenterDisjointness
import LeanTrominoes.PeriodicOrthocrossingContinuousParallel

/-!
# Constructed route interiors avoid lifted graph vertices

The track construction meets a declared graph vertex only at the first or
last point of an incident route.  Horizontal track rows are disjoint from the
vertex row, except for the short fanout segments; their sole interior lattice
point lies off every vertex center column.  Vertical port columns begin above
the vertex row, and private gate columns lie outside the vertex blocks.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 1200000
set_option maxRecDepth 4000

/-- No translated segment of the constructed drawing contains a lifted
declared graph vertex in its relative interior. -/
theorem drawingSegment_not_interiorContains_liftedVertexPosition
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {indexed : IndexedGridSegment}
    (indexedMem : indexed ∈ (drawing graph).indexedSegments)
    (routeTranslate : Cell)
    {vertex : Vertex}
    (vertexMem : vertex ∈ graph.vertices)
    (vertexTranslate : Cell) :
    ¬(indexed.segment.translate
        ((drawing graph).periodTranslation routeTranslate)).InteriorContains
      (Cell.add
        ((drawing graph).vertexPosition graph vertex)
        ((drawing graph).periodTranslation vertexTranslate)) := by
  intro contains
  rcases exists_classifiedSegment_of_drawing_mem indexedMem with
    ⟨taggedRoute, taggedRouteMem,
      taggedClassified, taggedClassifiedMem, indexedEq⟩
  have edgeMem :
      taggedRoute.1 ∈ graph.edges.zipIdx :=
    List.fst_mem_of_mem_zipIdx taggedRouteMem
  have classifiedMem :
      taggedClassified.1 ∈
        classifiedRouteSegments graph
          taggedRoute.1.1 taggedRoute.1.2 :=
    List.fst_mem_of_mem_zipIdx taggedClassifiedMem
  have classifiedContains :
      (taggedClassified.1.segment.translate
          ((drawing graph).periodTranslation routeTranslate)).InteriorContains
        (Cell.add
          ((drawing graph).vertexPosition graph vertex)
          ((drawing graph).periodTranslation vertexTranslate)) := by
    simpa [indexedEq] using contains
  have aligned :
      taggedClassified.1.segment.IsAxisAligned := by
    have indexedAligned :=
      drawing_isOrthogonal wellFormed isLocal degree
        indexed indexedMem
    simpa [indexedEq] using indexedAligned
  rcases aligned with horizontal | vertical
  · have translatedHorizontal :
        (taggedClassified.1.segment.translate
          ((drawing graph).periodTranslation routeTranslate)).IsHorizontal :=
      (GridSegment.isHorizontal_translate _ _).mpr horizontal
    have horizontalRole :=
      classifiedSegment_horizontalRole_of_isHorizontal
        classifiedMem horizontal
    have pointY :
        2 + (drawing graph).gridSize * vertexTranslate.2 =
          taggedClassified.1.segment.start.2 +
            drawingGridSize graph * routeTranslate.2 := by
      rcases classifiedContains with
        ⟨_horizontal, sameY, _between⟩ |
          ⟨translatedVertical, _sameX, _between⟩
      · rw [drawing_vertexPosition_of_mem graph vertexMem] at sameY
        simpa [GridSegment.translate,
          PeriodicGridDrawing.periodTranslation,
          drawing_gridSize, vertexPosition,
          Cell.add, Cell.scale, add_comm] using sameY
      · exact (translatedHorizontal.2 translatedVertical.1).elim
    have lane :=
      classifiedSegment_horizontal_lane
        classifiedMem horizontalRole
    have laneBounds :=
      horizontalLaneBase_bounds edgeMem classifiedMem horizontalRole
    have twoBounds :
        0 ≤ (2 : Int) ∧
          (2 : Int) < (drawing graph).gridSize := by
      rw [drawing_gridSize]
      have sizePositive := drawingGridSize_pos graph
      unfold drawingGridSize at sizePositive ⊢
      omega
    have laneBounds' :
        0 ≤ horizontalLaneBase taggedClassified.1.role ∧
          horizontalLaneBase taggedClassified.1.role <
            (drawing graph).gridSize := by
      simpa [drawing_gridSize] using laneBounds
    have lanePeriodicEqual :
        (2 : Int) +
            (drawing graph).gridSize * vertexTranslate.2 =
          horizontalLaneBase taggedClassified.1.role +
            (drawing graph).gridSize *
              (horizontalLaneCellShift taggedRoute.1.1
                taggedClassified.1.role + routeTranslate.2) := by
      rw [drawing_gridSize]
      rw [lane] at pointY
      simpa [mul_add, add_assoc] using pointY
    have laneBaseEqual :=
      ((drawing graph).translatedHalfOpenCoordinates_eq
        twoBounds laneBounds' lanePeriodicEqual).1
    have fanout :
        taggedClassified.1.role.IsHorizontalFanout := by
      cases roleEq : taggedClassified.1.role with
      | sourceFanoutHorizontal port =>
          simp [SegmentRole.IsHorizontalFanout]
      | sourceFanoutVertical port =>
          simp [roleEq, SegmentRole.IsHorizontalRole] at horizontalRole
      | sourcePortVertical port =>
          simp [roleEq, SegmentRole.IsHorizontalRole] at horizontalRole
      | lowHorizontal roleEdgeIndex =>
          simp [roleEq, horizontalLaneBase, edgeTrack] at laneBaseEqual
          omega
      | highHorizontal roleEdgeIndex =>
          simp [roleEq, horizontalLaneBase, edgeTrack] at laneBaseEqual
          omega
      | gateVertical roleEdgeIndex =>
          simp [roleEq, SegmentRole.IsHorizontalRole] at horizontalRole
      | boundaryVertical roleEdgeIndex =>
          simp [roleEq, SegmentRole.IsHorizontalRole] at horizontalRole
      | targetPortVertical port =>
          simp [roleEq, SegmentRole.IsHorizontalRole] at horizontalRole
      | targetFanoutVertical port =>
          simp [roleEq, SegmentRole.IsHorizontalRole] at horizontalRole
      | targetFanoutHorizontal port =>
          simp [SegmentRole.IsHorizontalFanout]
    rcases horizontalFanout_midpoint_of_interiorContains
        degree edgeMem classifiedMem fanout
        routeTranslate
        (Cell.add
          ((drawing graph).vertexPosition graph vertex)
          ((drawing graph).periodTranslation vertexTranslate))
        classifiedContains with
      ⟨port, portEq, portMem, midpointEqual⟩
    have midpointBounds :=
      fanoutMidpointBase_bounds
        wellFormed degree portEq portMem
    have vertexXBounds := vertexX_bounds vertexMem
    have vertexXBounds' :
        0 ≤ vertexX (graph.vertices.idxOf vertex) ∧
          vertexX (graph.vertices.idxOf vertex) <
            (drawing graph).gridSize := by
      simpa [drawing_gridSize] using
        ⟨le_of_lt vertexXBounds.1, vertexXBounds.2⟩
    have midpointBounds' :
        0 ≤ fanoutMidpointBase graph taggedClassified.1.role ∧
          fanoutMidpointBase graph taggedClassified.1.role <
            (drawing graph).gridSize := by
      simpa [drawing_gridSize] using midpointBounds
    have midpointPeriodicEqual :
        vertexX (graph.vertices.idxOf vertex) +
            (drawing graph).gridSize * vertexTranslate.1 =
          fanoutMidpointBase graph taggedClassified.1.role +
            (drawing graph).gridSize *
              ((horizontalFanoutCellShift taggedRoute.1.1
                taggedClassified.1.role).1 + routeTranslate.1) := by
      rw [drawing_vertexPosition_of_mem graph vertexMem] at midpointEqual
      cases roleEq : taggedClassified.1.role with
      | sourceFanoutHorizontal rolePort =>
          have rolePortEq : rolePort = port := by
            simpa [roleEq,
              SegmentRole.horizontalFanoutPort] using portEq
          subst port
          simpa [roleEq, fanoutMidpointBase,
            horizontalFanoutCellShift,
            PeriodicGridDrawing.periodTranslation,
            drawing_gridSize, vertexPosition,
            Cell.add, Cell.scale, mul_add,
            add_assoc] using midpointEqual
      | sourceFanoutVertical rolePort =>
          simp [roleEq, SegmentRole.IsHorizontalFanout] at fanout
      | sourcePortVertical rolePort =>
          simp [roleEq, SegmentRole.IsHorizontalFanout] at fanout
      | lowHorizontal roleEdgeIndex =>
          simp [roleEq, SegmentRole.IsHorizontalFanout] at fanout
      | highHorizontal roleEdgeIndex =>
          simp [roleEq, SegmentRole.IsHorizontalFanout] at fanout
      | gateVertical roleEdgeIndex =>
          simp [roleEq, SegmentRole.IsHorizontalFanout] at fanout
      | boundaryVertical roleEdgeIndex =>
          simp [roleEq, SegmentRole.IsHorizontalFanout] at fanout
      | targetPortVertical rolePort =>
          simp [roleEq, SegmentRole.IsHorizontalFanout] at fanout
      | targetFanoutVertical rolePort =>
          simp [roleEq, SegmentRole.IsHorizontalFanout] at fanout
      | targetFanoutHorizontal rolePort =>
          have rolePortEq : rolePort = port := by
            simpa [roleEq,
              SegmentRole.horizontalFanoutPort] using portEq
          subst port
          simpa [roleEq, fanoutMidpointBase,
            horizontalFanoutCellShift,
            PeriodicGridDrawing.periodTranslation,
            drawing_gridSize, vertexPosition,
            Cell.add, Cell.scale, mul_add,
            add_assoc] using midpointEqual
    have midpointBaseEqual :=
      ((drawing graph).translatedHalfOpenCoordinates_eq
        vertexXBounds' midpointBounds' midpointPeriodicEqual).1
    exact
      (classifiedSegment_horizontalFanout_midpoint_ne_vertexX
        degree classifiedMem fanout portEq portMem)
        midpointBaseEqual
  · have translatedVertical :
        (taggedClassified.1.segment.translate
          ((drawing graph).periodTranslation routeTranslate)).IsVertical :=
      (GridSegment.isVertical_translate _ _).mpr vertical
    have active :=
      classifiedSegment_activeVertical_of_interiorContains
        classifiedMem routeTranslate
        (Cell.add
          ((drawing graph).vertexPosition graph vertex)
          ((drawing graph).periodTranslation vertexTranslate))
        classifiedContains translatedVertical
    have lane :=
      classifiedSegment_vertical_lane classifiedMem active
    have pointX :
        vertexX (graph.vertices.idxOf vertex) +
            (drawing graph).gridSize * vertexTranslate.1 =
          taggedClassified.1.segment.start.1 +
            drawingGridSize graph * routeTranslate.1 := by
      rcases classifiedContains with
        ⟨translatedHorizontal, _sameY, _between⟩ |
          ⟨_vertical, sameX, _between⟩
      · exact (translatedVertical.2 translatedHorizontal.1).elim
      · rw [drawing_vertexPosition_of_mem graph vertexMem] at sameX
        simpa [GridSegment.translate,
          PeriodicGridDrawing.periodTranslation,
          drawing_gridSize, vertexPosition,
          Cell.add, Cell.scale, add_comm] using sameX
    have vertexXBounds := vertexX_bounds vertexMem
    have vertexXBounds' :
        0 ≤ vertexX (graph.vertices.idxOf vertex) ∧
          vertexX (graph.vertices.idxOf vertex) <
            (drawing graph).gridSize := by
      simpa [drawing_gridSize] using
        ⟨le_of_lt vertexXBounds.1, vertexXBounds.2⟩
    have laneBounds :=
      verticalLaneBase_bounds
        wellFormed degree edgeMem classifiedMem active
    have laneBounds' :
        0 ≤ verticalLaneBase graph taggedClassified.1.role ∧
          verticalLaneBase graph taggedClassified.1.role <
            (drawing graph).gridSize := by
      simpa [drawing_gridSize] using laneBounds
    have lanePeriodicEqual :
        vertexX (graph.vertices.idxOf vertex) +
            (drawing graph).gridSize * vertexTranslate.1 =
          verticalLaneBase graph taggedClassified.1.role +
            (drawing graph).gridSize *
              (verticalLaneCellShift taggedRoute.1.1
                taggedClassified.1.role + routeTranslate.1) := by
      rw [drawing_gridSize]
      rw [lane] at pointX
      simpa [mul_add, add_assoc] using pointX
    have laneBaseEqual :=
      ((drawing graph).translatedHalfOpenCoordinates_eq
        vertexXBounds' laneBounds' lanePeriodicEqual).1
    cases roleEq : taggedClassified.1.role with
    | sourcePortVertical port =>
        have yBounds :=
          classifiedSegment_sourcePortVertical_y_bounds
            edgeMem classifiedMem roleEq
        rcases yBounds with
          ⟨startYEq, finishYLower, finishYUpper⟩
        rcases classifiedContains with
          ⟨translatedHorizontal, _sameY, _between⟩ |
            ⟨_vertical, _sameX, between⟩
        · exact (translatedVertical.2 translatedHorizontal.1).elim
        · rw [drawing_vertexPosition_of_mem graph vertexMem] at between
          simp only [GridSegment.translate,
            PeriodicGridDrawing.periodTranslation,
            drawing_gridSize, vertexPosition,
            Cell.add, Cell.scale] at between
          rw [startYEq] at between
          have sizePositive := drawingGridSize_pos graph
          unfold GridSegment.StrictlyBetween at between
          rcases between with between | between
          · by_cases translateLe :
                vertexTranslate.2 ≤ routeTranslate.2
            · have productLe :=
                mul_le_mul_of_nonneg_left translateLe
                  (show (0 : Int) ≤ drawingGridSize graph by omega)
              nlinarith [productLe]
            · have translateGe :
                  routeTranslate.2 + 1 ≤ vertexTranslate.2 := by
                omega
              have productGe :=
                mul_le_mul_of_nonneg_left translateGe
                  (show (0 : Int) ≤ drawingGridSize graph by omega)
              have productGe' :
                  drawingGridSize graph * routeTranslate.2 +
                      drawingGridSize graph ≤
                    drawingGridSize graph * vertexTranslate.2 := by
                simpa [mul_add] using productGe
              nlinarith [productGe]
          · by_cases translateLe :
                vertexTranslate.2 ≤ routeTranslate.2
            · have productLe :=
                mul_le_mul_of_nonneg_left translateLe
                  (show (0 : Int) ≤ drawingGridSize graph by omega)
              omega
            · have translateGe :
                  routeTranslate.2 + 1 ≤ vertexTranslate.2 := by
                omega
              have productGe :=
                mul_le_mul_of_nonneg_left translateGe
                  (show (0 : Int) ≤ drawingGridSize graph by omega)
              have productGe' :
                  drawingGridSize graph * routeTranslate.2 +
                      drawingGridSize graph ≤
                    drawingGridSize graph * vertexTranslate.2 := by
                simpa [mul_add] using productGe
              omega
    | gateVertical roleEdgeIndex =>
        have vertexIndexLt :
            graph.vertices.idxOf vertex < graph.vertices.length :=
          List.idxOf_lt_length_iff.mpr vertexMem
        have roleIndex :=
          classifiedSegment_role_edgeIndex classifiedMem
        have roleEdgeIndexEq :
            roleEdgeIndex = taggedRoute.1.2 := by
          simpa [roleEq, SegmentRole.edgeIndex] using roleIndex
        subst roleEdgeIndex
        simp [roleEq, verticalLaneBase,
          edgeGateX, vertexX] at laneBaseEqual
        omega
    | targetPortVertical port =>
        have edgeLocal :
            taggedRoute.1.1.span ≤ 1 :=
          isLocal taggedRoute.1.1
            (List.fst_mem_of_mem_zipIdx edgeMem)
        have yBounds :=
          classifiedSegment_targetPortVertical_y_bounds
            edgeMem edgeLocal classifiedMem roleEq
        rcases yBounds with
          ⟨finishYEq, startYLower, startYUpper⟩
        rcases classifiedContains with
          ⟨translatedHorizontal, _sameY, _between⟩ |
            ⟨_vertical, _sameX, between⟩
        · exact (translatedVertical.2 translatedHorizontal.1).elim
        · rw [drawing_vertexPosition_of_mem graph vertexMem] at between
          simp only [GridSegment.translate,
            PeriodicGridDrawing.periodTranslation,
            drawing_gridSize, vertexPosition,
            Cell.add, Cell.scale] at between
          rw [finishYEq] at between
          have sizePositive := drawingGridSize_pos graph
          unfold GridSegment.StrictlyBetween at between
          rcases between with between | between
          · by_cases translateLe :
                vertexTranslate.2 ≤
                  taggedRoute.1.1.offset.2 + routeTranslate.2
            · have productLe :=
                mul_le_mul_of_nonneg_left translateLe
                  (show (0 : Int) ≤ drawingGridSize graph by omega)
              have productLe' :
                  drawingGridSize graph * vertexTranslate.2 ≤
                    drawingGridSize graph *
                        taggedRoute.1.1.offset.2 +
                      drawingGridSize graph * routeTranslate.2 := by
                simpa [mul_add] using productLe
              nlinarith [productLe]
            · have translateGe :
                  taggedRoute.1.1.offset.2 + routeTranslate.2 + 1 ≤
                    vertexTranslate.2 := by
                omega
              have productGe :=
                mul_le_mul_of_nonneg_left translateGe
                  (show (0 : Int) ≤ drawingGridSize graph by omega)
              have productGe' :
                  drawingGridSize graph *
                        taggedRoute.1.1.offset.2 +
                      drawingGridSize graph * routeTranslate.2 +
                        drawingGridSize graph ≤
                    drawingGridSize graph * vertexTranslate.2 := by
                calc
                  _ = drawingGridSize graph *
                      (taggedRoute.1.1.offset.2 +
                        routeTranslate.2 + 1) := by ring
                  _ ≤ _ := productGe
              nlinarith [productGe]
          · by_cases translateLe :
                vertexTranslate.2 ≤
                  taggedRoute.1.1.offset.2 + routeTranslate.2
            · have productLe :=
                mul_le_mul_of_nonneg_left translateLe
                  (show (0 : Int) ≤ drawingGridSize graph by omega)
              have productLe' :
                  drawingGridSize graph * vertexTranslate.2 ≤
                    drawingGridSize graph *
                        taggedRoute.1.1.offset.2 +
                      drawingGridSize graph * routeTranslate.2 := by
                simpa [mul_add] using productLe
              nlinarith [productLe]
            · have translateGe :
                  taggedRoute.1.1.offset.2 + routeTranslate.2 + 1 ≤
                    vertexTranslate.2 := by
                omega
              have productGe :=
                mul_le_mul_of_nonneg_left translateGe
                  (show (0 : Int) ≤ drawingGridSize graph by omega)
              have productGe' :
                  drawingGridSize graph *
                        taggedRoute.1.1.offset.2 +
                      drawingGridSize graph * routeTranslate.2 +
                        drawingGridSize graph ≤
                    drawingGridSize graph * vertexTranslate.2 := by
                calc
                  _ = drawingGridSize graph *
                      (taggedRoute.1.1.offset.2 +
                        routeTranslate.2 + 1) := by ring
                  _ ≤ _ := productGe
              nlinarith [productGe]
    | sourceFanoutHorizontal port =>
        simp [roleEq, SegmentRole.IsActiveVertical] at active
    | sourceFanoutVertical port =>
        simp [roleEq, SegmentRole.IsActiveVertical] at active
    | lowHorizontal roleEdgeIndex =>
        simp [roleEq, SegmentRole.IsActiveVertical] at active
    | highHorizontal roleEdgeIndex =>
        simp [roleEq, SegmentRole.IsActiveVertical] at active
    | boundaryVertical roleEdgeIndex =>
        simp [roleEq, SegmentRole.IsActiveVertical] at active
    | targetFanoutVertical port =>
        simp [roleEq, SegmentRole.IsActiveVertical] at active
    | targetFanoutHorizontal port =>
        simp [roleEq, SegmentRole.IsActiveVertical] at active

/-- The constructed drawing satisfies the periodic graph-vertex avoidance
half of planar route geometry. -/
theorem drawing_verticesAvoidRouteInteriors
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal) :
    (drawing graph).VerticesAvoidRouteInteriors := by
  intro vertexPosition vertexPositionMem indexed indexedMem
    vertexTranslate routeTranslate
  rcases List.mem_map.mp vertexPositionMem with
    ⟨taggedVertex, taggedVertexMem, vertexPositionEq⟩
  have vertexMem :
      taggedVertex.1 ∈ graph.vertices :=
    List.fst_mem_of_mem_zipIdx taggedVertexMem
  have taggedIndexLt :
      taggedVertex.2 < graph.vertices.length :=
    List.snd_lt_of_mem_zipIdx taggedVertexMem
  have taggedGet :
      graph.vertices.get ⟨taggedVertex.2, taggedIndexLt⟩ =
        taggedVertex.1 := by
    exact (List.mem_zipIdx' taggedVertexMem).2.symm
  have taggedIndexEq :
      graph.vertices.idxOf taggedVertex.1 = taggedVertex.2 := by
    have indexed :=
      List.get_idxOf wellFormed.1
        (⟨taggedVertex.2, taggedIndexLt⟩ :
          Fin graph.vertices.length)
    rw [taggedGet] at indexed
    simpa using indexed
  have positionEq :
      vertexPosition =
        (drawing graph).vertexPosition graph taggedVertex.1 := by
    rw [drawing_vertexPosition_of_mem graph vertexMem,
      taggedIndexEq]
    exact vertexPositionEq.symm
  rw [positionEq]
  exact
    drawingSegment_not_interiorContains_liftedVertexPosition
      wellFormed degree isLocal indexedMem routeTranslate
      vertexMem vertexTranslate

end PeriodicOrthocrossing
end LeanTrominoes
