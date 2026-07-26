import LeanTrominoes.PeriodicGridDrawingContinuousPlanarity

/-!
# Positive integral scaling of grid-drawing geometry

Local gadget substitution repeatedly refines every drawing cell by a positive
integer factor.  This file records the elementary geometry once: scaling
commutes with translating segments and taking polyline segments, and it
preserves all axis-aligned containment and continuous-intersection tests.
-/

namespace LeanTrominoes

namespace Cell

/-- Coordinatewise scaling distributes over coordinatewise addition. -/
theorem scale_add (factor : Int) (first second : Cell) :
    scale factor (add first second) =
      add (scale factor first) (scale factor second) := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp [scale, add]
  constructor <;> ring

/-- Successive coordinatewise scalings multiply their factors. -/
theorem scale_scale (first second : Int) (point : Cell) :
    scale first (scale second point) =
      scale (first * second) point := by
  rcases point with ⟨pointX, pointY⟩
  simp [scale]
  constructor <;> ring

/-- Scaling by a nonzero integer is injective on lattice points. -/
theorem scale_injective {factor : Int} (nonzero : factor ≠ 0) :
    Function.Injective (scale factor) := by
  rintro ⟨firstX, firstY⟩ ⟨secondX, secondY⟩ equality
  simp only [scale, Prod.mk.injEq] at equality ⊢
  exact
    ⟨mul_left_cancel₀ nonzero equality.1,
      mul_left_cancel₀ nonzero equality.2⟩

end Cell

namespace GridSegment

/-- Scale both endpoints of a grid segment about the origin. -/
def scale (factor : Int) (segment : GridSegment) : GridSegment :=
  ⟨Cell.scale factor segment.start, Cell.scale factor segment.finish⟩

@[simp]
theorem scale_start (factor : Int) (segment : GridSegment) :
    (segment.scale factor).start = Cell.scale factor segment.start :=
  rfl

@[simp]
theorem scale_finish (factor : Int) (segment : GridSegment) :
    (segment.scale factor).finish = Cell.scale factor segment.finish :=
  rfl

/-- Scaling commutes with segment translation. -/
theorem scale_translate (factor : Int) (offset : Cell)
    (segment : GridSegment) :
    (segment.translate offset).scale factor =
      (segment.scale factor).translate (Cell.scale factor offset) := by
  rcases segment with ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases offset with ⟨offsetX, offsetY⟩
  simp [scale, translate, Cell.scale, Cell.add]
  constructor <;> constructor <;> ring

/-- A positive scale factor preserves horizontalness exactly. -/
@[simp]
theorem isHorizontal_scale_iff
    {factor : Int} (positive : 0 < factor) (segment : GridSegment) :
    (segment.scale factor).IsHorizontal ↔ segment.IsHorizontal := by
  rcases segment with ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  simp [scale, Cell.scale, IsHorizontal, positive.ne']

/-- A positive scale factor preserves verticalness exactly. -/
@[simp]
theorem isVertical_scale_iff
    {factor : Int} (positive : 0 < factor) (segment : GridSegment) :
    (segment.scale factor).IsVertical ↔ segment.IsVertical := by
  rcases segment with ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  simp [scale, Cell.scale, IsVertical, positive.ne']

/-- A positive scale factor preserves orthogonality exactly. -/
@[simp]
theorem isAxisAligned_scale_iff
    {factor : Int} (positive : 0 < factor) (segment : GridSegment) :
    (segment.scale factor).IsAxisAligned ↔ segment.IsAxisAligned := by
  simp [IsAxisAligned, isHorizontal_scale_iff positive,
    isVertical_scale_iff positive]

/-- Positive scaling preserves strict one-dimensional betweenness. -/
@[simp]
theorem strictlyBetween_mul_iff
    {factor : Int} (positive : 0 < factor)
    (first finish point : Int) :
    StrictlyBetween (factor * first) (factor * finish) (factor * point) ↔
      StrictlyBetween first finish point := by
  simp [StrictlyBetween, Int.mul_lt_mul_left positive]

/-- Positive scaling preserves closed one-dimensional betweenness. -/
@[simp]
theorem between_mul_iff
    {factor : Int} (positive : 0 < factor)
    (first finish point : Int) :
    Between (factor * first) (factor * finish) (factor * point) ↔
      Between first finish point := by
  simp [Between, Int.mul_le_mul_left positive]

/-- Positive scaling preserves relative-interior containment. -/
@[simp]
theorem interiorContains_scale_iff
    {factor : Int} (positive : 0 < factor)
    (segment : GridSegment) (point : Cell) :
    (segment.scale factor).InteriorContains (Cell.scale factor point) ↔
      segment.InteriorContains point := by
  simp only [InteriorContains, scale_start]
  rw [isHorizontal_scale_iff positive, isVertical_scale_iff positive]
  rcases segment with ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases point with ⟨pointX, pointY⟩
  simp [Cell.scale, strictlyBetween_mul_iff positive, positive.ne']

/-- Positive scaling preserves closed segment containment. -/
@[simp]
theorem contains_scale_iff
    {factor : Int} (positive : 0 < factor)
    (segment : GridSegment) (point : Cell) :
    (segment.scale factor).Contains (Cell.scale factor point) ↔
      segment.Contains point := by
  simp only [Contains, scale_start]
  rw [isHorizontal_scale_iff positive, isVertical_scale_iff positive]
  rcases segment with ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases point with ⟨pointX, pointY⟩
  simp [Cell.scale, between_mul_iff positive, positive.ne']

/-- Positive scaling preserves overlap of open integer intervals. -/
@[simp]
theorem openIntervalsOverlap_mul_iff
    {factor : Int} (positive : 0 < factor)
    (firstStart firstFinish secondStart secondFinish : Int) :
    OpenIntervalsOverlap
        (factor * firstStart) (factor * firstFinish)
        (factor * secondStart) (factor * secondFinish) ↔
      OpenIntervalsOverlap
        firstStart firstFinish secondStart secondFinish := by
  have nonnegative : 0 ≤ factor := positive.le
  unfold OpenIntervalsOverlap
  rw [← mul_min_of_nonneg firstStart firstFinish nonnegative,
    ← mul_max_of_nonneg secondStart secondFinish nonnegative,
    ← mul_min_of_nonneg secondStart secondFinish nonnegative,
    ← mul_max_of_nonneg firstStart firstFinish nonnegative]
  simp [Int.mul_lt_mul_left positive]

/-- Positive scaling preserves continuous relative-interior intersection. -/
@[simp]
theorem interiorsMeet_scale_iff
    {factor : Int} (positive : 0 < factor)
    (first second : GridSegment) :
    InteriorsMeet (first.scale factor) (second.scale factor) ↔
      InteriorsMeet first second := by
  simp only [InteriorsMeet, isHorizontal_scale_iff positive,
    isVertical_scale_iff positive, scale_start, scale_finish]
  rcases first with
    ⟨⟨firstStartX, firstStartY⟩, ⟨firstFinishX, firstFinishY⟩⟩
  rcases second with
    ⟨⟨secondStartX, secondStartY⟩, ⟨secondFinishX, secondFinishY⟩⟩
  simp [Cell.scale, openIntervalsOverlap_mul_iff positive,
    strictlyBetween_mul_iff positive, positive.ne']

end GridSegment

/-- Scale every point of a grid polyline about the origin. -/
def scalePolyline (factor : Int) (route : List Cell) : List Cell :=
  route.map (Cell.scale factor)

@[simp]
theorem scalePolyline_nil (factor : Int) :
    scalePolyline factor [] = [] :=
  rfl

@[simp]
theorem scalePolyline_cons (factor : Int) (point : Cell)
    (route : List Cell) :
    scalePolyline factor (point :: route) =
      Cell.scale factor point :: scalePolyline factor route :=
  rfl

/-- Consecutive segments of a scaled polyline are precisely the scaled
consecutive segments of the original. -/
theorem gridPolylineSegments_scalePolyline
    (factor : Int) (route : List Cell) :
    gridPolylineSegments (scalePolyline factor route) =
      (gridPolylineSegments route).map (GridSegment.scale factor) := by
  induction route using List.twoStepInduction with
  | nil | singleton => rfl
  | cons_cons first second rest _ tailInduction =>
      simp only [scalePolyline_cons, gridPolylineSegments, List.map_cons]
      apply congrArg₂ List.cons
      · rfl
      · exact tailInduction second

@[simp]
theorem scalePolyline_head?
    (factor : Int) (route : List Cell) :
    (scalePolyline factor route).head? =
      route.head?.map (Cell.scale factor) := by
  cases route <;> rfl

@[simp]
theorem scalePolyline_getLast?
    (factor : Int) (route : List Cell) :
    (scalePolyline factor route).getLast? =
      route.getLast?.map (Cell.scale factor) := by
  simp [scalePolyline]

namespace IndexedGridSegment

/-- Scale an indexed segment without changing its syntactic occurrence
indices. -/
def scale (factor : Int)
    (indexed : IndexedGridSegment) : IndexedGridSegment where
  routeIndex := indexed.routeIndex
  segmentIndex := indexed.segmentIndex
  segment := indexed.segment.scale factor

@[simp]
theorem scale_routeIndex (factor : Int)
    (indexed : IndexedGridSegment) :
    (indexed.scale factor).routeIndex = indexed.routeIndex :=
  rfl

@[simp]
theorem scale_segmentIndex (factor : Int)
    (indexed : IndexedGridSegment) :
    (indexed.scale factor).segmentIndex = indexed.segmentIndex :=
  rfl

@[simp]
theorem scale_segment (factor : Int)
    (indexed : IndexedGridSegment) :
    (indexed.scale factor).segment =
      indexed.segment.scale factor :=
  rfl

end IndexedGridSegment

namespace PeriodicGridDrawing

/-- Refine a complete periodic drawing by a natural scale factor.  The
positive-factor theorems below identify its new side length with the old
side length times `factor`; the total definition keeps factor zero harmless. -/
def scale (factor : Nat) (drawing : PeriodicGridDrawing) :
    PeriodicGridDrawing where
  gridSizePred := factor * drawing.gridSize - 1
  vertexPositions :=
    drawing.vertexPositions.map (Cell.scale factor)
  edgeRoutes :=
    drawing.edgeRoutes.map (scalePolyline factor)

/-- A positive refinement multiplies the fundamental-square side length. -/
@[simp]
theorem gridSize_scale {factor : Nat} (positive : 0 < factor)
    (drawing : PeriodicGridDrawing) :
    (drawing.scale factor).gridSize = factor * drawing.gridSize := by
  change factor * drawing.gridSize - 1 + 1 =
    factor * drawing.gridSize
  have productPositive : 0 < factor * (drawing.gridSizePred + 1) :=
    Nat.mul_pos positive (by omega)
  exact Nat.sub_add_cancel productPositive

/-- The scaled drawing's lattice translation is the scaled old
translation. -/
theorem periodTranslation_scale
    {factor : Nat} (positive : 0 < factor)
    (drawing : PeriodicGridDrawing) (translate : Cell) :
    (drawing.scale factor).periodTranslation translate =
      Cell.scale factor (drawing.periodTranslation translate) := by
  rcases translate with ⟨translateX, translateY⟩
  simp [periodTranslation, gridSize_scale positive,
    Cell.scale]
  constructor <;> ring

/-- Vertex lookup commutes with positive drawing refinement. -/
theorem vertexPosition_scale
    {Vertex : Type*} [BEq Vertex]
    (factor : Nat) (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) (vertex : Vertex) :
    (drawing.scale factor).vertexPosition graph vertex =
      Cell.scale factor (drawing.vertexPosition graph vertex) := by
  unfold vertexPosition scale
  change
    (drawing.vertexPositions.map (Cell.scale factor)).getD
        (graph.vertices.idxOf vertex) (Cell.scale factor (0, 0)) =
      Cell.scale factor
        (drawing.vertexPositions.getD
          (graph.vertices.idxOf vertex) (0, 0))
  rw [List.getD_map]

/-- Edge-route lookup commutes with drawing refinement. -/
theorem edgeRoute_scale
    (factor : Nat) (drawing : PeriodicGridDrawing)
    (edgeIndex : Nat) :
    (drawing.scale factor).edgeRoute edgeIndex =
      scalePolyline factor (drawing.edgeRoute edgeIndex) := by
  unfold edgeRoute scale
  change
    (drawing.edgeRoutes.map (scalePolyline factor)).getD
        edgeIndex (scalePolyline factor []) =
      scalePolyline factor
        (drawing.edgeRoutes.getD edgeIndex [])
  rw [List.getD_map]

/-- The indexed segment list of a refined drawing has exactly the original
occurrence keys and the scaled segment geometry. -/
theorem indexedSegments_scale
    (factor : Nat) (drawing : PeriodicGridDrawing) :
    (drawing.scale factor).indexedSegments =
      drawing.indexedSegments.map
        (IndexedGridSegment.scale factor) := by
  unfold indexedSegments scale
  rw [List.zipIdx_map, List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  rintro ⟨route, routeIndex⟩ taggedRouteMember
  simp [gridPolylineSegments_scalePolyline,
    List.zipIdx_map, List.map_map,
    IndexedGridSegment.scale, Function.comp_def]

/-- Positive refinement preserves membership in the open fundamental
square exactly. -/
theorem positionInFundamentalSquare_scale_iff
    {factor : Nat} (positive : 0 < factor)
    (drawing : PeriodicGridDrawing) (position : Cell) :
    (drawing.scale factor).PositionInFundamentalSquare
        (Cell.scale factor position) ↔
      drawing.PositionInFundamentalSquare position := by
  rcases position with ⟨horizontal, vertical⟩
  simp only [PositionInFundamentalSquare, Cell.scale,
    gridSize_scale positive]
  norm_cast
  simp [positive]

/-- A positive refinement preserves exact graph endpoints. -/
theorem routesMatch_scale
    {Vertex : Type*} [BEq Vertex]
    {factor : Nat} (positive : 0 < factor)
    (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing)
    (routeMatches : drawing.RoutesMatch graph) :
    (drawing.scale factor).RoutesMatch graph := by
  intro taggedEdge taggedEdgeMember
  have endpoints := routeMatches taggedEdge taggedEdgeMember
  constructor
  · rw [edgeRoute_scale, scalePolyline_head?, endpoints.1]
    simp [vertexPosition_scale]
  · rw [edgeRoute_scale, scalePolyline_getLast?, endpoints.2]
    simp only [Option.map_some]
    rw [vertexPosition_scale, periodTranslation_scale positive,
      Cell.scale_add]

/-- Positive refinement preserves complete graph compatibility. -/
theorem isCompatible_scale
    {Vertex : Type*} [DecidableEq Vertex]
    {factor : Nat} (positive : 0 < factor)
    (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing)
    (compatible : drawing.IsCompatible graph) :
    (drawing.scale factor).IsCompatible graph := by
  rcases compatible with
    ⟨wellFormed, vertexLength, routeLength, positionsNodup,
      positionBounds, routesMatch⟩
  refine
    ⟨wellFormed, ?_, ?_, ?_, ?_,
      routesMatch_scale positive graph drawing routesMatch⟩
  · simpa [scale] using vertexLength
  · simpa [scale] using routeLength
  · exact positionsNodup.map
      (Cell.scale_injective (by positivity : (factor : Int) ≠ 0))
  · intro scaledPosition scaledPositionMember
    rcases List.mem_map.mp scaledPositionMember with
      ⟨position, positionMember, rfl⟩
    exact
      (positionInFundamentalSquare_scale_iff
        positive drawing position).mpr
        (positionBounds position positionMember)

/-- Positive refinement preserves orthogonality of every route segment. -/
theorem isOrthogonal_scale
    {factor : Nat} (positive : 0 < factor)
    (drawing : PeriodicGridDrawing)
    (orthogonal : drawing.IsOrthogonal) :
    (drawing.scale factor).IsOrthogonal := by
  intro scaledIndexed scaledIndexedMember
  rw [indexedSegments_scale] at scaledIndexedMember
  rcases List.mem_map.mp scaledIndexedMember with
    ⟨indexed, indexedMember, rfl⟩
  exact
    (GridSegment.isAxisAligned_scale_iff
      (by exact_mod_cast positive) indexed.segment).mpr
      (orthogonal indexed indexedMember)

end PeriodicGridDrawing

end LeanTrominoes
