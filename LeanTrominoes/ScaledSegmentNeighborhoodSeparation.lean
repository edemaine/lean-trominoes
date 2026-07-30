import LeanTrominoes.ScaledPointNeighborhoodSeparation

/-!
# Separation from a bounded segment neighborhood after scaling

The point-neighborhood theorem has a segment analogue for an axis-aligned
reference segment.  Integral closed segments that are contact-free have
coordinate rectangles separated by at least one lattice unit.  Uniform
scaling turns that unit into enough room for a fixed-radius route around
the scaled reference segment.
-/

namespace LeanTrominoes

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Two contact-free axis-aligned integral segments have strictly separated
endpoint rectangles. -/
theorem GridSegment.coordinateRectangles_separated_of_axisAligned
    {first second : GridSegment}
    (firstAligned : first.IsAxisAligned)
    (secondAligned : second.IsAxisAligned)
    (interiorsAvoid :
      ¬GridSegment.InteriorsMeet first second)
    (firstStartAvoid :
      ¬second.InteriorContains first.start)
    (firstFinishAvoid :
      ¬second.InteriorContains first.finish)
    (secondStartAvoid :
      ¬first.InteriorContains second.start)
    (secondFinishAvoid :
      ¬first.InteriorContains second.finish)
    (startStartNe : first.start ≠ second.start)
    (startFinishNe : first.start ≠ second.finish)
    (finishStartNe : first.finish ≠ second.start)
    (finishFinishNe : first.finish ≠ second.finish) :
    ClosedGridRectanglesSeparated
      first.coordinateLower first.coordinateUpper
      second.coordinateLower second.coordinateUpper := by
  rcases first with
    ⟨⟨firstStartX, firstStartY⟩,
      ⟨firstFinishX, firstFinishY⟩⟩
  rcases second with
    ⟨⟨secondStartX, secondStartY⟩,
      ⟨secondFinishX, secondFinishY⟩⟩
  simp only [GridSegment.IsAxisAligned,
    GridSegment.IsHorizontal, GridSegment.IsVertical]
    at firstAligned secondAligned
  rcases firstAligned with firstHorizontal | firstVertical <;>
    rcases secondAligned with secondHorizontal | secondVertical
  all_goals
    simp only [GridSegment.InteriorsMeet,
      GridSegment.InteriorContains,
      GridSegment.IsHorizontal, GridSegment.IsVertical,
      GridSegment.OpenIntervalsOverlap,
      GridSegment.StrictlyBetween,
      GridSegment.coordinateLower,
      GridSegment.coordinateUpper,
      ClosedGridRectanglesSeparated] at *
    simp_all [min_def, max_def] <;> omega

/-- Scaling separated integral rectangles leaves room for a coordinate
radius expansion around the second scaled rectangle. -/
theorem ClosedGridRectanglesSeparated.scale_left_rectangle_radius
    {firstLower firstUpper secondLower secondUpper : Cell}
    {factor radius : Nat}
    (separated :
      ClosedGridRectanglesSeparated
        firstLower firstUpper secondLower secondUpper)
    (factorPositive : 0 < factor)
    (radiusLt : radius < factor) :
    ClosedGridRectanglesSeparated
      (Cell.scale factor firstLower)
      (Cell.scale factor firstUpper)
      (coordinateRadiusLower radius
        (Cell.scale factor secondLower))
      (coordinateRadiusUpper radius
        (Cell.scale factor secondUpper)) := by
  rcases firstLower with ⟨firstLowerX, firstLowerY⟩
  rcases firstUpper with ⟨firstUpperX, firstUpperY⟩
  rcases secondLower with ⟨secondLowerX, secondLowerY⟩
  rcases secondUpper with ⟨secondUpperX, secondUpperY⟩
  have factorNonnegativeInt :
      (0 : Int) ≤ factor := by
    exact_mod_cast factorPositive.le
  have radiusLtInt :
      (radius : Int) < factor := by
    exact_mod_cast radiusLt
  simp only [ClosedGridRectanglesSeparated,
    coordinateRadiusLower, coordinateRadiusUpper,
    Cell.scale] at separated ⊢
  rcases separated with
      forwardX | backwardX | forwardY | backwardY
  · left
    have gap : firstUpperX + 1 ≤ secondLowerX := by
      omega
    have scaled :=
      mul_le_mul_of_nonneg_left gap factorNonnegativeInt
    rw [mul_add] at scaled
    omega
  · right
    left
    have gap : secondUpperX + 1 ≤ firstLowerX := by
      omega
    have scaled :=
      mul_le_mul_of_nonneg_left gap factorNonnegativeInt
    rw [mul_add] at scaled
    omega
  · right
    right
    left
    have gap : firstUpperY + 1 ≤ secondLowerY := by
      omega
    have scaled :=
      mul_le_mul_of_nonneg_left gap factorNonnegativeInt
    rw [mul_add] at scaled
    omega
  · right
    right
    right
    have gap : secondUpperY + 1 ≤ firstLowerY := by
      omega
    have scaled :=
      mul_le_mul_of_nonneg_left gap factorNonnegativeInt
    rw [mul_add] at scaled
    omega

/-- A finite source route strictly separated from an axis-aligned integral
segment remains strictly separated, after scaling, from every route in a
smaller coordinate-radius neighborhood of that scaled segment. -/
theorem
    routesStrictlyAvoidEachOther_scalePolyline_axisAlignedSegmentNeighborhood
    {source nearby : List Cell}
    {reference : GridSegment}
    {factor radius : Nat}
    (factorPositive : 0 < factor)
    (radiusLt : radius < factor)
    (referenceAligned : reference.IsAxisAligned)
    (sourceAvoids :
      RoutesStrictlyAvoidEachOther
        source [reference.start, reference.finish])
    (nearbyBounded :
      ∀ point ∈ nearby,
        InClosedGridRectangle
          (coordinateRadiusLower radius
            (Cell.scale factor reference.coordinateLower))
          (coordinateRadiusUpper radius
            (Cell.scale factor reference.coordinateUpper))
          point) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline factor source) nearby := by
  have factorPositiveInt :
      (0 : Int) < factor := by
    exact_mod_cast factorPositive
  have factorNonnegativeInt :
      (0 : Int) ≤ factor :=
    factorPositiveInt.le
  have referenceMember :
      reference ∈
        gridPolylineSegments
          [reference.start, reference.finish] := by
    simp [gridPolylineSegments]
  have sourcePointSeparated :
      ∀ point ∈ source,
        ClosedGridRectanglesSeparated
          point point
          reference.coordinateLower
          reference.coordinateUpper := by
    intro point pointMember
    have notContained : ¬reference.Contains point := by
      intro contains
      rcases
          GridSegment.interiorContains_or_eq_start_or_eq_finish_of_contains
            contains with
        interior | endpoint
      · exact
          (sourceAvoids.2.1
            point pointMember reference referenceMember)
            interior
      · rcases endpoint with atStart | atFinish
        · exact
            (sourceAvoids.2.2.2
              point pointMember reference.start
              (by simp))
              atStart
        · exact
            (sourceAvoids.2.2.2
              point pointMember reference.finish
              (by simp))
              atFinish
    exact
      (reference.coordinateRectangle_separated_point
        referenceAligned notContained).symm
  have sourceSegmentSeparated :
      ∀ segment ∈ gridPolylineSegments source,
        segment.IsAxisAligned →
          ClosedGridRectanglesSeparated
            segment.coordinateLower segment.coordinateUpper
            reference.coordinateLower
            reference.coordinateUpper := by
    intro segment segmentMember segmentAligned
    have endpoints :=
      gridPolylineSegments_endpoints_mem segmentMember
    exact
      GridSegment.coordinateRectangles_separated_of_axisAligned
        segmentAligned referenceAligned
        (sourceAvoids.1
          segment segmentMember reference referenceMember)
        (sourceAvoids.2.1
          segment.start endpoints.1 reference referenceMember)
        (sourceAvoids.2.1
          segment.finish endpoints.2 reference referenceMember)
        (sourceAvoids.2.2.1
          reference.start (by simp) segment segmentMember)
        (sourceAvoids.2.2.1
          reference.finish (by simp) segment segmentMember)
        (sourceAvoids.2.2.2
          segment.start endpoints.1 reference.start (by simp))
        (sourceAvoids.2.2.2
          segment.start endpoints.1 reference.finish (by simp))
        (sourceAvoids.2.2.2
          segment.finish endpoints.2 reference.start (by simp))
        (sourceAvoids.2.2.2
          segment.finish endpoints.2 reference.finish (by simp))
  unfold RoutesStrictlyAvoidEachOther
  rw [gridPolylineSegments_scalePolyline]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro scaledSourceSegment scaledSourceMember
      nearbySegment nearbySegmentMember
    rcases List.mem_map.mp scaledSourceMember with
      ⟨sourceSegment, sourceSegmentMember, rfl⟩
    by_cases aligned : sourceSegment.IsAxisAligned
    · have separated :=
        (sourceSegmentSeparated
          sourceSegment sourceSegmentMember aligned)
          |>.scale_left_rectangle_radius
            factorPositive radiusLt
      have nearbyEndpoints :=
        gridPolylineSegments_endpoints_mem nearbySegmentMember
      exact
        not_interiorsMeet_of_inClosedGridRectangles_of_separated
          (sourceSegment.start_in_coordinateRectangle.scale
            factorNonnegativeInt)
          (sourceSegment.finish_in_coordinateRectangle.scale
            factorNonnegativeInt)
          (nearbyBounded _ nearbyEndpoints.1)
          (nearbyBounded _ nearbyEndpoints.2)
          separated
    · intro meet
      apply aligned
      have scaledAligned :
          (sourceSegment.scale factor).IsAxisAligned := by
        rcases meet with
            horizontal | vertical |
            horizontalVertical | verticalHorizontal
        · exact Or.inl horizontal.1
        · exact Or.inr vertical.1
        · exact Or.inl horizontalVertical.1
        · exact Or.inr verticalHorizontal.1
      exact
        (GridSegment.isAxisAligned_scale_iff
          factorPositiveInt sourceSegment).mp scaledAligned
  · intro scaledSourcePoint scaledSourcePointMember
      nearbySegment nearbySegmentMember
    rcases List.mem_map.mp scaledSourcePointMember with
      ⟨sourcePoint, sourcePointMember, rfl⟩
    have separated :=
      (sourcePointSeparated sourcePoint sourcePointMember)
        |>.scale_left_rectangle_radius
          factorPositive radiusLt
    have nearbyEndpoints :=
      gridPolylineSegments_endpoints_mem nearbySegmentMember
    exact
      not_interiorContains_of_inClosedGridRectangles_of_separated
        (by exact ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩)
        (nearbyBounded _ nearbyEndpoints.1)
        (nearbyBounded _ nearbyEndpoints.2)
        separated
  · intro nearbyPoint nearbyPointMember
      scaledSourceSegment scaledSourceMember
    rcases List.mem_map.mp scaledSourceMember with
      ⟨sourceSegment, sourceSegmentMember, rfl⟩
    by_cases aligned : sourceSegment.IsAxisAligned
    · have separated :=
        (sourceSegmentSeparated
          sourceSegment sourceSegmentMember aligned)
          |>.scale_left_rectangle_radius
            factorPositive radiusLt
      exact
        not_interiorContains_of_inClosedGridRectangles_of_separated
          (nearbyBounded _ nearbyPointMember)
          (sourceSegment.start_in_coordinateRectangle.scale
            factorNonnegativeInt)
          (sourceSegment.finish_in_coordinateRectangle.scale
            factorNonnegativeInt)
          separated.symm
    · intro contains
      apply aligned
      have scaledAligned :
          (sourceSegment.scale factor).IsAxisAligned :=
        contains.elim
          (fun horizontal => Or.inl horizontal.1)
          (fun vertical => Or.inr vertical.1)
      exact
        (GridSegment.isAxisAligned_scale_iff
          factorPositiveInt sourceSegment).mp scaledAligned
  · intro scaledSourcePoint scaledSourcePointMember
      nearbyPoint nearbyPointMember
    rcases List.mem_map.mp scaledSourcePointMember with
      ⟨sourcePoint, sourcePointMember, rfl⟩
    have separated :=
      (sourcePointSeparated sourcePoint sourcePointMember)
        |>.scale_left_rectangle_radius
          factorPositive radiusLt
    exact
      ne_of_inClosedGridRectangles_of_separated
        (by exact ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩)
        (nearbyBounded _ nearbyPointMember)
        separated

end LeanTrominoes
