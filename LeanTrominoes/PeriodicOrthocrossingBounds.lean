import LeanTrominoes.PeriodicOrthocrossingCertified

/-!
# Coordinate bounds for the constructed drawing

Every stored route point lies in the three-by-three block of drawing cells
centered on the fundamental square.  Consequently, an occurrence meeting the
fundamental square can use only a neighboring cell translation.  These bounds
make the crossing set used by planarization finitely enumerable.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

/-- A point lies strictly between `-M` and `2M` in both coordinates. -/
def InExpandedDrawingSquare {Vertex : Type*}
    (graph : PeriodicGraph Vertex) (point : Cell) : Prop :=
  -(drawingGridSize graph : Int) < point.1 ∧
    point.1 < 2 * drawingGridSize graph ∧
    -(drawingGridSize graph : Int) < point.2 ∧
    point.2 < 2 * drawingGridSize graph

/-- Half-open canonical representative square for crossing points. -/
def InFundamentalDrawingSquare {Vertex : Type*}
    (graph : PeriodicGraph Vertex) (point : Cell) : Prop :=
  0 ≤ point.1 ∧ point.1 < drawingGridSize graph ∧
    0 ≤ point.2 ∧ point.2 < drawingGridSize graph

/-- The nine cell translations neighboring the canonical square. -/
def IsNeighborTranslation (translate : Cell) : Prop :=
  (translate.1 = -1 ∨ translate.1 = 0 ∨ translate.1 = 1) ∧
    (translate.2 = -1 ∨ translate.2 = 0 ∨ translate.2 = 1)

/-- A translated lane representative from the expanded square can meet the
canonical square only at a neighboring cell translation. -/
theorem lane_shift_is_neighbor
    {period base shift point : Int}
    (periodPositive : 0 < period)
    (baseLower : -period < base)
    (baseUpper : base < 2 * period)
    (pointLower : 0 ≤ point)
    (pointUpper : point < period)
    (equal : point = base + period * shift) :
    shift = -1 ∨ shift = 0 ∨ shift = 1 := by
  have notTooLow : ¬shift ≤ -2 := by
    intro shiftLow
    have nonnegative :
        0 ≤ period * (-shift - 2) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productUpper : period * shift ≤ -2 * period := by
      nlinarith
    omega
  have notTooHigh : ¬2 ≤ shift := by
    intro shiftHigh
    have nonnegative :
        0 ≤ period * (shift - 2) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productLower : 2 * period ≤ period * shift := by
      nlinarith
    omega
  omega

/-- The same neighboring-translation bound holds when the canonical point
lies strictly between two translated expanded-square coordinates. -/
theorem between_shift_is_neighbor
    {period first last shift point : Int}
    (periodPositive : 0 < period)
    (firstLower : -period < first)
    (firstUpper : first < 2 * period)
    (lastLower : -period < last)
    (lastUpper : last < 2 * period)
    (pointLower : 0 ≤ point)
    (pointUpper : point < period)
    (between :
      GridSegment.StrictlyBetween
        (first + period * shift)
        (last + period * shift) point) :
    shift = -1 ∨ shift = 0 ∨ shift = 1 := by
  have notTooLow : ¬shift ≤ -2 := by
    intro shiftLow
    have nonnegative :
        0 ≤ period * (-shift - 2) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productUpper : period * shift ≤ -2 * period := by
      nlinarith
    unfold GridSegment.StrictlyBetween at between
    rcases between with between | between <;>
      omega
  have notTooHigh : ¬2 ≤ shift := by
    intro shiftHigh
    have nonnegative :
        0 ≤ period * (shift - 2) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productLower : 2 * period ≤ period * shift := by
      nlinarith
    unfold GridSegment.StrictlyBetween at between
    rcases between with between | between <;>
      omega
  omega

/-- Every listed protovertex center lies strictly inside the fundamental
drawing square. -/
theorem vertexX_bounds
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {vertex : Vertex}
    (vertexMem : vertex ∈ graph.vertices) :
    0 < vertexX (graph.vertices.idxOf vertex) ∧
      vertexX (graph.vertices.idxOf vertex) < drawingGridSize graph := by
  have indexLt :
      graph.vertices.idxOf vertex < graph.vertices.length :=
    List.idxOf_lt_length_iff.mpr vertexMem
  unfold vertexX drawingGridSize
  omega

/-- Both endpoints of every classified local route segment lie in the
expanded three-by-three drawing square. -/
theorem classifiedSegment_endpoints_inExpandedDrawingSquare
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
    (edgeMem : (edge, edgeIndex) ∈ graph.edges.zipIdx)
    (edgeLocal : edge.span ≤ 1)
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex) :
    InExpandedDrawingSquare graph classified.segment.start ∧
      InExpandedDrawingSquare graph classified.segment.finish := by
  have endpoints :=
    wellFormed.2 edge
      (List.fst_mem_of_mem_zipIdx edgeMem)
  have sourceVertexBounds := vertexX_bounds endpoints.1
  have targetVertexBounds := vertexX_bounds endpoints.2
  have sourceMem := sourcePort_mem_allPorts graph edgeMem
  have targetMem := targetPort_mem_allPorts graph edgeMem
  have sourceBounds := portX_bounds wellFormed degree sourceMem
  have targetBounds := portX_bounds wellFormed degree targetMem
  have sourceBounds' :
      0 < portX graph (sourcePort edge edgeIndex) ∧
        portX graph (sourcePort edge edgeIndex) < drawingGridSize graph := by
    simpa using sourceBounds
  have targetBounds' :
      0 < portX graph (targetPort edge edgeIndex) ∧
        portX graph (targetPort edge edgeIndex) < drawingGridSize graph := by
    simpa using targetBounds
  have tracks := edgeTrack_bounds graph edgeMem
  have tracks' :
      3 < edgeTrack edgeIndex ∧
        edgeTrack edgeIndex + 1 < drawingGridSize graph := by
    simpa using tracks
  have gateBounds := edgeGateX_bounds graph edgeMem
  have gateBounds' :
      0 < edgeGateX graph edgeIndex ∧
        edgeGateX graph edgeIndex < drawingGridSize graph := by
    simpa using gateBounds
  have periodPositive : (0 : Int) < drawingGridSize graph := by
    exact_mod_cast drawingGridSize_pos graph
  rcases offset_eq_of_span_le_one edge edgeLocal with
    offsetZero | offsetRight | offsetLeft | offsetUp | offsetDown
  · have sourceAll :
        ∀ item ∈ classifiedSourceFanout graph edge edgeIndex,
          InExpandedDrawingSquare graph item.segment.start ∧
            InExpandedDrawingSquare graph item.segment.finish := by
      simp [classifiedSourceFanout, InExpandedDrawingSquare]
      split <;> simp_all <;> omega
    have coreAll :
        ∀ item ∈ classifiedEdgeCore graph edge edgeIndex,
          InExpandedDrawingSquare graph item.segment.start ∧
            InExpandedDrawingSquare graph item.segment.finish := by
      simp [classifiedEdgeCore, offsetZero,
        InExpandedDrawingSquare, Cell.add, Cell.scale]
      omega
    have targetAll :
        ∀ item ∈ classifiedTargetFanout graph edge edgeIndex,
          InExpandedDrawingSquare graph item.segment.start ∧
            InExpandedDrawingSquare graph item.segment.finish := by
      simp [classifiedTargetFanout, offsetZero,
        InExpandedDrawingSquare, Cell.add, Cell.scale]
      split <;> simp_all <;> omega
    simp only [classifiedRouteSegments, List.mem_append] at classifiedMem
    exact classifiedMem.elim
      (fun sourceOrCore => sourceOrCore.elim
        (fun sourceClassified =>
          sourceAll classified sourceClassified)
        (fun coreClassified =>
          coreAll classified coreClassified))
      (fun targetClassified =>
        targetAll classified targetClassified)
  · have sourceAll :
        ∀ item ∈ classifiedSourceFanout graph edge edgeIndex,
          InExpandedDrawingSquare graph item.segment.start ∧
            InExpandedDrawingSquare graph item.segment.finish := by
      simp [classifiedSourceFanout, InExpandedDrawingSquare]
      split <;> simp_all <;> omega
    have coreAll :
        ∀ item ∈ classifiedEdgeCore graph edge edgeIndex,
          InExpandedDrawingSquare graph item.segment.start ∧
            InExpandedDrawingSquare graph item.segment.finish := by
      simp [classifiedEdgeCore, offsetRight,
        InExpandedDrawingSquare, Cell.add, Cell.scale]
      split <;> simp_all <;> omega
    have targetAll :
        ∀ item ∈ classifiedTargetFanout graph edge edgeIndex,
          InExpandedDrawingSquare graph item.segment.start ∧
            InExpandedDrawingSquare graph item.segment.finish := by
      simp [classifiedTargetFanout, offsetRight,
        InExpandedDrawingSquare, Cell.add, Cell.scale]
      split <;> simp_all <;> omega
    simp only [classifiedRouteSegments, List.mem_append] at classifiedMem
    exact classifiedMem.elim
      (fun sourceOrCore => sourceOrCore.elim
        (fun sourceClassified =>
          sourceAll classified sourceClassified)
        (fun coreClassified =>
          coreAll classified coreClassified))
      (fun targetClassified =>
        targetAll classified targetClassified)
  · have sourceAll :
        ∀ item ∈ classifiedSourceFanout graph edge edgeIndex,
          InExpandedDrawingSquare graph item.segment.start ∧
            InExpandedDrawingSquare graph item.segment.finish := by
      simp [classifiedSourceFanout, InExpandedDrawingSquare]
      split <;> simp_all <;> omega
    have coreAll :
        ∀ item ∈ classifiedEdgeCore graph edge edgeIndex,
          InExpandedDrawingSquare graph item.segment.start ∧
            InExpandedDrawingSquare graph item.segment.finish := by
      simp [classifiedEdgeCore, offsetLeft,
        InExpandedDrawingSquare, Cell.add, Cell.scale]
      split <;> simp_all <;> omega
    have targetAll :
        ∀ item ∈ classifiedTargetFanout graph edge edgeIndex,
          InExpandedDrawingSquare graph item.segment.start ∧
            InExpandedDrawingSquare graph item.segment.finish := by
      simp [classifiedTargetFanout, offsetLeft,
        InExpandedDrawingSquare, Cell.add, Cell.scale]
      split <;> simp_all <;> omega
    simp only [classifiedRouteSegments, List.mem_append] at classifiedMem
    exact classifiedMem.elim
      (fun sourceOrCore => sourceOrCore.elim
        (fun sourceClassified =>
          sourceAll classified sourceClassified)
        (fun coreClassified =>
          coreAll classified coreClassified))
      (fun targetClassified =>
        targetAll classified targetClassified)
  · have sourceAll :
        ∀ item ∈ classifiedSourceFanout graph edge edgeIndex,
          InExpandedDrawingSquare graph item.segment.start ∧
            InExpandedDrawingSquare graph item.segment.finish := by
      simp [classifiedSourceFanout, InExpandedDrawingSquare]
      split <;> simp_all <;> omega
    have coreAll :
        ∀ item ∈ classifiedEdgeCore graph edge edgeIndex,
          InExpandedDrawingSquare graph item.segment.start ∧
            InExpandedDrawingSquare graph item.segment.finish := by
      simp [classifiedEdgeCore, offsetUp,
        InExpandedDrawingSquare, Cell.add, Cell.scale]
      omega
    have targetAll :
        ∀ item ∈ classifiedTargetFanout graph edge edgeIndex,
          InExpandedDrawingSquare graph item.segment.start ∧
            InExpandedDrawingSquare graph item.segment.finish := by
      simp [classifiedTargetFanout, offsetUp,
        InExpandedDrawingSquare, Cell.add, Cell.scale]
      split <;> simp_all <;> omega
    simp only [classifiedRouteSegments, List.mem_append] at classifiedMem
    exact classifiedMem.elim
      (fun sourceOrCore => sourceOrCore.elim
        (fun sourceClassified =>
          sourceAll classified sourceClassified)
        (fun coreClassified =>
          coreAll classified coreClassified))
      (fun targetClassified =>
        targetAll classified targetClassified)
  · have sourceAll :
        ∀ item ∈ classifiedSourceFanout graph edge edgeIndex,
          InExpandedDrawingSquare graph item.segment.start ∧
            InExpandedDrawingSquare graph item.segment.finish := by
      simp [classifiedSourceFanout, InExpandedDrawingSquare]
      split <;> simp_all <;> omega
    have coreAll :
        ∀ item ∈ classifiedEdgeCore graph edge edgeIndex,
          InExpandedDrawingSquare graph item.segment.start ∧
            InExpandedDrawingSquare graph item.segment.finish := by
      simp [classifiedEdgeCore, offsetDown,
        InExpandedDrawingSquare, Cell.add, Cell.scale]
      omega
    have targetAll :
        ∀ item ∈ classifiedTargetFanout graph edge edgeIndex,
          InExpandedDrawingSquare graph item.segment.start ∧
            InExpandedDrawingSquare graph item.segment.finish := by
      simp [classifiedTargetFanout, offsetDown,
        InExpandedDrawingSquare, Cell.add, Cell.scale]
      split <;> simp_all <;> omega
    simp only [classifiedRouteSegments, List.mem_append] at classifiedMem
    exact classifiedMem.elim
      (fun sourceOrCore => sourceOrCore.elim
        (fun sourceClassified =>
          sourceAll classified sourceClassified)
        (fun coreClassified =>
          coreAll classified coreClassified))
      (fun targetClassified =>
        targetAll classified targetClassified)

/-- The coordinate bound transfers from semantic classified segments to the
indexed segment enumeration exposed by the drawing API. -/
theorem drawing_indexedSegment_endpoints_inExpandedDrawingSquare
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {indexed : IndexedGridSegment}
    (indexedMem : indexed ∈ (drawing graph).indexedSegments) :
    InExpandedDrawingSquare graph indexed.segment.start ∧
      InExpandedDrawingSquare graph indexed.segment.finish := by
  rcases exists_classifiedSegment_of_drawing_mem indexedMem with
    ⟨route, routeMem, classified, classifiedMem, indexedEq⟩
  subst indexed
  have edgeMem :
      (route.1.1, route.1.2) ∈ graph.edges.zipIdx :=
    List.fst_mem_of_mem_zipIdx routeMem
  exact classifiedSegment_endpoints_inExpandedDrawingSquare
    wellFormed degree edgeMem
      (isLocal route.1.1 (List.fst_mem_of_mem_zipIdx edgeMem))
      (List.fst_mem_of_mem_zipIdx classifiedMem)

/-- An occurrence whose interior meets the canonical square is necessarily
one of the nine neighboring translates of its stored segment. -/
theorem drawing_occurrence_translate_isNeighbor
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {indexed : IndexedGridSegment}
    (indexedMem : indexed ∈ (drawing graph).indexedSegments)
    {translate point : Cell}
    (pointFundamental : InFundamentalDrawingSquare graph point)
    (contains :
      (indexed.segment.translate
        ((drawing graph).periodTranslation translate)).InteriorContains
          point) :
    IsNeighborTranslation translate := by
  have endpointBounds :=
    drawing_indexedSegment_endpoints_inExpandedDrawingSquare
      wellFormed degree isLocal indexedMem
  have periodPositive : (0 : Int) < drawingGridSize graph := by
    exact_mod_cast drawingGridSize_pos graph
  rcases endpointBounds with ⟨startBounds, finishBounds⟩
  rcases startBounds with
    ⟨startXLower, startXUpper, startYLower, startYUpper⟩
  rcases finishBounds with
    ⟨finishXLower, finishXUpper, finishYLower, finishYUpper⟩
  rcases pointFundamental with
    ⟨pointXLower, pointXUpper, pointYLower, pointYUpper⟩
  rcases contains with
    ⟨horizontal, pointYEq, pointXBetween⟩ |
      ⟨vertical, pointXEq, pointYBetween⟩
  · have pointYEq' :
        point.2 =
          indexed.segment.start.2 +
            drawingGridSize graph * translate.2 := by
      simpa [GridSegment.translate,
        PeriodicGridDrawing.periodTranslation, drawing_gridSize,
        Cell.add, Cell.scale, add_comm] using pointYEq
    have pointXBetween' :
        GridSegment.StrictlyBetween
          (indexed.segment.start.1 +
            drawingGridSize graph * translate.1)
          (indexed.segment.finish.1 +
            drawingGridSize graph * translate.1)
          point.1 := by
      simpa [GridSegment.translate,
        PeriodicGridDrawing.periodTranslation, drawing_gridSize,
        Cell.add, Cell.scale, add_comm] using pointXBetween
    exact ⟨between_shift_is_neighbor
        periodPositive startXLower startXUpper
        finishXLower finishXUpper pointXLower pointXUpper
        pointXBetween',
      lane_shift_is_neighbor
        periodPositive startYLower startYUpper
        pointYLower pointYUpper pointYEq'⟩
  · have pointXEq' :
        point.1 =
          indexed.segment.start.1 +
            drawingGridSize graph * translate.1 := by
      simpa [GridSegment.translate,
        PeriodicGridDrawing.periodTranslation, drawing_gridSize,
        Cell.add, Cell.scale, add_comm] using pointXEq
    have pointYBetween' :
        GridSegment.StrictlyBetween
          (indexed.segment.start.2 +
            drawingGridSize graph * translate.2)
          (indexed.segment.finish.2 +
            drawingGridSize graph * translate.2)
          point.2 := by
      simpa [GridSegment.translate,
        PeriodicGridDrawing.periodTranslation, drawing_gridSize,
        Cell.add, Cell.scale, add_comm] using pointYBetween
    exact ⟨lane_shift_is_neighbor
        periodPositive startXLower startXUpper
        pointXLower pointXUpper pointXEq',
      between_shift_is_neighbor
        periodPositive startYLower startYUpper
        finishYLower finishYUpper pointYLower pointYUpper
        pointYBetween'⟩

end PeriodicOrthocrossing
end LeanTrominoes
