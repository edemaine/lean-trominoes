import LeanTrominoes.RetainedAngularFanOuterCorridor
import LeanTrominoes.RetainedRayRasterizationSeparation

/-!
# Coordinate-radius bounds for retained-ray rasterization

Retained-ray rasterization replaces each source segment by a staircase that
stays within coordinate radius nine of a checkpoint on that segment.  This
module converts that local corridor certificate into a whole-polyline bound:
if every source point is within radius `r` of one center, every rasterized
point is within radius `r + 9` of the same center.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- A checkpoint in the coordinate rectangle between two radius-bounded
endpoints is bounded by the same radius. -/
theorem withinCoordinateRadius_of_segmentCheckpoint
    {radius : Nat} {center : Cell}
    {segment : GridSegment}
    (startBounded :
      WithinCoordinateRadius radius center segment.start)
    (finishBounded :
      WithinCoordinateRadius radius center segment.finish)
    {primitive : Cell} {length index : Nat}
    (vector :
      Cell.sub segment.finish segment.start =
        Cell.scale length primitive)
    (indexBound : index ≤ length) :
    WithinCoordinateRadius radius center
      (Cell.add segment.start
        (Cell.scale index primitive)) := by
  have checkpointBounded :=
    retainedSegmentCheckpoint_in_coordinateRectangle
      segment primitive length index vector indexBound
  rcases startBounded.coordinate_bounds with
    ⟨⟨startHorizontalLower, startHorizontalUpper⟩,
      ⟨startVerticalLower, startVerticalUpper⟩⟩
  rcases finishBounded.coordinate_bounds with
    ⟨⟨finishHorizontalLower, finishHorizontalUpper⟩,
      ⟨finishVerticalLower, finishVerticalUpper⟩⟩
  rcases center with ⟨centerX, centerY⟩
  rcases segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases primitive with ⟨primitiveX, primitiveY⟩
  change centerX - (radius : Int) ≤ startX at startHorizontalLower
  change startX ≤ centerX + (radius : Int) at startHorizontalUpper
  change centerY - (radius : Int) ≤ startY at startVerticalLower
  change startY ≤ centerY + (radius : Int) at startVerticalUpper
  change centerX - (radius : Int) ≤ finishX at finishHorizontalLower
  change finishX ≤ centerX + (radius : Int) at finishHorizontalUpper
  change centerY - (radius : Int) ≤ finishY at finishVerticalLower
  change finishY ≤ centerY + (radius : Int) at finishVerticalUpper
  have horizontal :
      centerX - radius ≤
          startX + (index : Int) * primitiveX ∧
        startX + (index : Int) * primitiveX ≤
          centerX + radius := by
    simp only [InClosedGridRectangle,
      GridSegment.coordinateLower,
      GridSegment.coordinateUpper,
      Cell.add, Cell.scale] at checkpointBounded
    simp only [min_def, max_def] at checkpointBounded
    omega
  have vertical :
      centerY - radius ≤
          startY + (index : Int) * primitiveY ∧
        startY + (index : Int) * primitiveY ≤
          centerY + radius := by
    simp only [InClosedGridRectangle,
      GridSegment.coordinateLower,
      GridSegment.coordinateUpper,
      Cell.add, Cell.scale] at checkpointBounded
    simp only [min_def, max_def] at checkpointBounded
    omega
  have natAbsLe
      {delta : Int}
      (bounded : -(radius : Int) ≤ delta ∧
        delta ≤ (radius : Int)) :
      delta.natAbs ≤ radius := by
    by_cases nonnegative : 0 ≤ delta
    · have castBound :
          (delta.natAbs : Int) ≤ (radius : Int) := by
        rw [Int.natAbs_of_nonneg nonnegative]
        exact bounded.2
      exact_mod_cast castBound
    · have negativeNonnegative : 0 ≤ -delta := by
        omega
      have castBound :
          ((-delta).natAbs : Int) ≤ (radius : Int) := by
        rw [Int.natAbs_of_nonneg negativeNonnegative]
        omega
      have negativeBound : (-delta).natAbs ≤ radius := by
        exact_mod_cast castBound
      simpa using negativeBound
  simp only [WithinCoordinateRadius, Cell.add, Cell.scale]
  constructor
  · apply natAbsLe
    omega
  · apply natAbsLe
    omega

/-- Retained-ray rasterization enlarges a common coordinate-radius bound by
at most its uniform radius-nine staircase deviation. -/
theorem rasterizeRetainedPolyline_points_withinCoordinateRadius
    {radius : Nat} {center : Cell} {points : List Cell}
    (retained : RetainedRayPolyline points)
    (length : 2 ≤ points.length)
    (sourceBounded :
      ∀ point ∈ points,
        WithinCoordinateRadius radius center point)
    {point : Cell}
    (pointMember :
      point ∈ rasterizeRetainedPolyline points) :
    WithinCoordinateRadius (radius + 9) center point := by
  rcases
      rasterizeRetainedPolyline_point_in_corridor
        retained length pointMember with
    ⟨segment, segmentMember, primitive, segmentLength,
      index, segmentLengthPositive, vector, indexBound,
      pointNearCheckpoint⟩
  have endpoints :=
    gridPolylineSegments_endpoints_mem segmentMember
  have checkpointBounded :=
    withinCoordinateRadius_of_segmentCheckpoint
      (sourceBounded segment.start endpoints.1)
      (sourceBounded segment.finish endpoints.2)
      vector indexBound
  exact checkpointBounded.trans pointNearCheckpoint

/-- A retained-ray rasterization expands any common closed rectangle for the
source polyline by at most nine cells in every coordinate.  The statement
also covers empty and singleton polylines. -/
theorem rasterizeRetainedPolyline_point_in_expandedRectangle
    {lower upper : Cell} {points : List Cell}
    (retained : RetainedRayPolyline points)
    (sourceBounded :
      ∀ point ∈ points,
        InClosedGridRectangle lower upper point)
    {point : Cell}
    (pointMember :
      point ∈ rasterizeRetainedPolyline points) :
    InClosedGridRectangle
      (coordinateRadiusLower 9 lower)
      (coordinateRadiusUpper 9 upper)
      point := by
  by_cases length : 2 ≤ points.length
  · rcases
        rasterizeRetainedPolyline_point_in_corridor
          retained length pointMember with
      ⟨segment, segmentMember, corridor⟩
    have segmentBounded :=
      inExpandedCoordinateRectangle_of_inRetainedSegmentRasterCorridor
        corridor
    have endpoints :=
      gridPolylineSegments_endpoints_mem segmentMember
    have startBounded :=
      sourceBounded segment.start endpoints.1
    have finishBounded :=
      sourceBounded segment.finish endpoints.2
    rcases lower with ⟨lowerX, lowerY⟩
    rcases upper with ⟨upperX, upperY⟩
    rcases segment with
      ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
    rcases point with ⟨pointX, pointY⟩
    simp only [InClosedGridRectangle,
      coordinateRadiusLower, coordinateRadiusUpper,
      GridSegment.coordinateLower,
      GridSegment.coordinateUpper]
      at startBounded finishBounded segmentBounded ⊢
    omega
  · rcases points with _ | ⟨first, rest⟩
    · simp [rasterizeRetainedPolyline] at pointMember
    · rcases rest with _ | ⟨second, rest⟩
      · simp only [rasterizeRetainedPolyline_singleton,
          List.mem_singleton] at pointMember
        subst point
        have firstBounded := sourceBounded first (by simp)
        rcases lower with ⟨lowerX, lowerY⟩
        rcases upper with ⟨upperX, upperY⟩
        rcases first with ⟨firstX, firstY⟩
        simp only [InClosedGridRectangle,
          coordinateRadiusLower, coordinateRadiusUpper]
          at firstBounded ⊢
        omega
      · simp at length

end PeriodicEightOccurrenceSplit
end LeanTrominoes
