import LeanTrominoes.PeriodicGridDrawingContinuousPlanarity

/-!
# Positive integral scaling of grid-drawing geometry

Local gadget substitution repeatedly refines every drawing cell by a positive
integer factor.  This file records the elementary geometry once: scaling
commutes with translating segments and taking polyline segments, and it
preserves all axis-aligned containment and continuous-intersection tests.
-/

namespace LeanTrominoes

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

end LeanTrominoes
