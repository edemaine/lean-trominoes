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
    ⟨startHorizontal, startVertical⟩
  rcases finishBounded.coordinate_bounds with
    ⟨finishHorizontal, finishVertical⟩
  rcases center with ⟨centerX, centerY⟩
  rcases segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases primitive with ⟨primitiveX, primitiveY⟩
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
  simp only [WithinCoordinateRadius, Cell.add, Cell.scale]
  constructor
  · rw [Int.natAbs_le]
    omega
  · rw [Int.natAbs_le]
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

end PeriodicEightOccurrenceSplit
end LeanTrominoes
