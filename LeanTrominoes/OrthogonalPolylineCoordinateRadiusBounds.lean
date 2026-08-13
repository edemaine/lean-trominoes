/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineLoopErasure
import LeanTrominoes.RetainedRayRasterizationCorridor

/-!
# Coordinate-radius bounds under orthogonal loop erasure

Closed coordinate-radius squares are orthogonally convex: an axis-aligned
segment whose endpoints lie in the square lies entirely in the square.
Every point retained by orthogonal route normalization lies on an original
segment, so any translated pointwise radius bound survives normalization.
-/

namespace LeanTrominoes

open PeriodicEightOccurrenceSplit

namespace PeriodicEightOccurrenceSplit

/-- Coordinate-radius containment expressed using integer absolute values. -/
theorem withinCoordinateRadius_iff_abs_le
    {radius : Nat} {center point : Cell} :
    WithinCoordinateRadius radius center point ↔
      |point.1 - center.1| ≤ (radius : Int) ∧
        |point.2 - center.2| ≤ (radius : Int) := by
  constructor
  · intro bounded
    constructor
    · rw [← Int.natCast_natAbs]
      exact_mod_cast bounded.1
    · rw [← Int.natCast_natAbs]
      exact_mod_cast bounded.2
  · intro bounded
    constructor
    · have := bounded.1
      rw [← Int.natCast_natAbs] at this
      exact_mod_cast this
    · have := bounded.2
      rw [← Int.natCast_natAbs] at this
      exact_mod_cast this

/-- A closed axis-aligned segment between radius-bounded endpoints remains
inside the same coordinate-radius square. -/
theorem WithinCoordinateRadius.of_segment_contains
    {radius : Nat} {center : Cell}
    {segment : GridSegment} {point : Cell}
    (startBounded :
      WithinCoordinateRadius radius center segment.start)
    (finishBounded :
      WithinCoordinateRadius radius center segment.finish)
    (contains : segment.Contains point) :
    WithinCoordinateRadius radius center point := by
  rw [withinCoordinateRadius_iff_abs_le] at startBounded finishBounded ⊢
  have startHorizontal := (abs_le.mp startBounded.1)
  have startVertical := (abs_le.mp startBounded.2)
  have finishHorizontal := (abs_le.mp finishBounded.1)
  have finishVertical := (abs_le.mp finishBounded.2)
  apply And.intro <;> apply abs_le.mpr
  · rcases contains with
      ⟨horizontal, same, between⟩ | ⟨vertical, same, between⟩
    · rcases between with forward | backward <;> omega
    · simp only [GridSegment.IsVertical] at vertical
      omega
  · rcases contains with
      ⟨horizontal, same, between⟩ | ⟨vertical, same, between⟩
    · simp only [GridSegment.IsHorizontal] at horizontal
      omega
    · rcases between with forward | backward <;> omega

end PeriodicEightOccurrenceSplit

namespace AxisDirection

/-- If a common translation of every original route point is radius-bounded,
the same translated bound holds for every point retained by orthogonal loop
erasure and unit subdivision. -/
theorem normalizeOrthogonalPolyline_points_withinCoordinateRadius
    {points : List Cell}
    (nonempty : points ≠ [])
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points)
    (offset : Cell) {radius : Nat} (center : Cell)
    (bounded :
      ∀ point ∈ points,
        WithinCoordinateRadius radius center
          (Cell.add offset point))
    {point : Cell}
    (pointMember : point ∈ normalizeOrthogonalPolyline points) :
    WithinCoordinateRadius radius center
      (Cell.add offset point) := by
  have subdividedMember :
      point ∈ unitSubdividePolyline points :=
    (normalizeOrthogonalPolyline_sublist_unitSubdividePolyline
      nonempty orthogonal).subset pointMember
  rcases unitSubdividePolyline_mem_original_or_segmentInterior
      orthogonal subdividedMember with
    originalMember | ⟨segment, segmentMember, interior⟩
  · exact bounded point originalMember
  · have endpointMembers :=
      gridPolylineSegments_endpoints_mem segmentMember
    have startBounded := bounded segment.start endpointMembers.1
    have finishBounded := bounded segment.finish endpointMembers.2
    let translatedSegment := segment.translate offset
    have translatedContains :
        translatedSegment.Contains (Cell.add offset point) := by
      simpa [Cell.add, add_comm] using
        (PeriodicGridDrawing.contains_translate_iff
          segment offset point).2
            (GridSegment.contains_of_interiorContains interior)
    exact WithinCoordinateRadius.of_segment_contains
      (by simpa [translatedSegment, GridSegment.translate] using
        startBounded)
      (by simpa [translatedSegment, GridSegment.translate] using
        finishBounded)
      translatedContains

end AxisDirection
end LeanTrominoes
