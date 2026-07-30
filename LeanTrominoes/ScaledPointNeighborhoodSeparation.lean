import LeanTrominoes.OrthogonalPolylineBoundingBox
import LeanTrominoes.RetainedAngularFanOuterRadialSeparation

/-!
# Separation from a bounded neighborhood after scaling

An integral point outside an axis-aligned source segment is separated from
that segment by at least one lattice unit.  Positive uniform scaling turns
this into a gap of one scale factor.  This file packages the resulting
clearance theorem for an arbitrary finite route lying in a smaller
coordinate-radius neighborhood of the scaled point.

Non-axis-aligned source segments need no quantitative argument here:
`RoutesStrictlyAvoidEachOther` only asks about horizontal and vertical
segment interiors, so only its axis-aligned source segments can participate
in one of those contacts.
-/

namespace LeanTrominoes

open PeriodicEightOccurrenceSplit

/-- Lower corner of the closed coordinate-radius square around a point. -/
def coordinateRadiusLower
    (radius : Nat) (center : Cell) : Cell :=
  (center.1 - radius, center.2 - radius)

/-- Upper corner of the closed coordinate-radius square around a point. -/
def coordinateRadiusUpper
    (radius : Nat) (center : Cell) : Cell :=
  (center.1 + radius, center.2 + radius)

/-- A coordinate-radius bound is the corresponding closed-rectangle
bound. -/
theorem inClosedGridRectangle_coordinateRadius
    {radius : Nat} {center point : Cell}
    (bounded : WithinCoordinateRadius radius center point) :
    InClosedGridRectangle
      (coordinateRadiusLower radius center)
      (coordinateRadiusUpper radius center)
      point := by
  rcases bounded.coordinate_bounds with
    ⟨horizontal, vertical⟩
  exact
    ⟨horizontal.1, horizontal.2,
      vertical.1, vertical.2⟩

/-- Lower coordinate corner of a segment's endpoint rectangle. -/
def GridSegment.coordinateLower
    (segment : GridSegment) : Cell :=
  (min segment.start.1 segment.finish.1,
    min segment.start.2 segment.finish.2)

/-- Upper coordinate corner of a segment's endpoint rectangle. -/
def GridSegment.coordinateUpper
    (segment : GridSegment) : Cell :=
  (max segment.start.1 segment.finish.1,
    max segment.start.2 segment.finish.2)

/-- A segment's first endpoint lies in its endpoint rectangle. -/
theorem GridSegment.start_in_coordinateRectangle
    (segment : GridSegment) :
    InClosedGridRectangle
      segment.coordinateLower
      segment.coordinateUpper
      segment.start := by
  simp [GridSegment.coordinateLower,
    GridSegment.coordinateUpper,
    InClosedGridRectangle]

/-- A segment's second endpoint lies in its endpoint rectangle. -/
theorem GridSegment.finish_in_coordinateRectangle
    (segment : GridSegment) :
    InClosedGridRectangle
      segment.coordinateLower
      segment.coordinateUpper
      segment.finish := by
  simp [GridSegment.coordinateLower,
    GridSegment.coordinateUpper,
    InClosedGridRectangle]

/-- Positive scaling transports a closed-rectangle bound. -/
theorem InClosedGridRectangle.scale
    {lower upper point : Cell}
    {factor : Int} (factorNonnegative : 0 ≤ factor)
    (bounded :
      InClosedGridRectangle lower upper point) :
    InClosedGridRectangle
      (Cell.scale factor lower)
      (Cell.scale factor upper)
      (Cell.scale factor point) := by
  rcases lower with ⟨lowerX, lowerY⟩
  rcases upper with ⟨upperX, upperY⟩
  rcases point with ⟨pointX, pointY⟩
  simp only [InClosedGridRectangle] at bounded ⊢
  simp only [Cell.scale]
  exact
    ⟨mul_le_mul_of_nonneg_left bounded.1 factorNonnegative,
      mul_le_mul_of_nonneg_left bounded.2.1 factorNonnegative,
      mul_le_mul_of_nonneg_left bounded.2.2.1 factorNonnegative,
      mul_le_mul_of_nonneg_left bounded.2.2.2
        factorNonnegative⟩

/-- An axis-aligned segment's endpoint rectangle is separated from every
integral point that the segment does not contain. -/
theorem GridSegment.coordinateRectangle_separated_point
    {segment : GridSegment} {point : Cell}
    (aligned : segment.IsAxisAligned)
    (notContained : ¬segment.Contains point) :
    ClosedGridRectanglesSeparated
      segment.coordinateLower segment.coordinateUpper
      point point := by
  rcases segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases point with ⟨pointX, pointY⟩
  simp only [GridSegment.IsAxisAligned,
    GridSegment.IsHorizontal, GridSegment.IsVertical]
    at aligned
  rcases aligned with horizontal | vertical
  · have sameY := horizontal.1
    subst finishY
    by_cases pointSameY : pointY = startY
    · subst pointY
      have notBetween :
          ¬GridSegment.Between
            startX finishX pointX := by
        intro between
        apply notContained
        exact Or.inl
          ⟨horizontal, rfl, between⟩
      rcases le_total startX finishX with
          forward | backward
      · simp only [GridSegment.Between] at notBetween
        simp only [ClosedGridRectanglesSeparated,
          GridSegment.coordinateLower,
          GridSegment.coordinateUpper,
          min_eq_left forward, max_eq_right forward,
          min_self, max_self]
        omega
      · simp only [GridSegment.Between] at notBetween
        simp only [ClosedGridRectanglesSeparated,
          GridSegment.coordinateLower,
          GridSegment.coordinateUpper,
          min_eq_right backward, max_eq_left backward,
          min_self, max_self]
        omega
    · rcases lt_or_gt_of_ne pointSameY with
          pointBelow | pointAbove
      · exact Or.inr (Or.inr (Or.inr (by
          simpa [GridSegment.coordinateLower,
            GridSegment.coordinateUpper]
            using pointBelow)))
      · exact Or.inr (Or.inr (Or.inl (by
          simpa [GridSegment.coordinateLower,
            GridSegment.coordinateUpper]
            using pointAbove)))
  · have sameX := vertical.1
    subst finishX
    by_cases pointSameX : pointX = startX
    · subst pointX
      have notBetween :
          ¬GridSegment.Between
            startY finishY pointY := by
        intro between
        apply notContained
        exact Or.inr
          ⟨vertical, rfl, between⟩
      rcases le_total startY finishY with
          forward | backward
      · simp only [GridSegment.Between] at notBetween
        simp only [ClosedGridRectanglesSeparated,
          GridSegment.coordinateLower,
          GridSegment.coordinateUpper,
          min_eq_left forward, max_eq_right forward,
          min_self, max_self]
        omega
      · simp only [GridSegment.Between] at notBetween
        simp only [ClosedGridRectanglesSeparated,
          GridSegment.coordinateLower,
          GridSegment.coordinateUpper,
          min_eq_right backward, max_eq_left backward,
          min_self, max_self]
        omega
    · rcases lt_or_gt_of_ne pointSameX with
          pointLeft | pointRight
      · exact Or.inr (Or.inl (by
          simpa [GridSegment.coordinateLower,
            GridSegment.coordinateUpper]
            using pointLeft))
      · exact Or.inl (by
          simpa [GridSegment.coordinateLower,
            GridSegment.coordinateUpper]
            using pointRight)

/-- Distinct integral points define separated singleton rectangles. -/
theorem closedGridSingletons_separated_of_ne
    {first second : Cell}
    (different : first ≠ second) :
    ClosedGridRectanglesSeparated
      first first second second := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [ClosedGridRectanglesSeparated]
  by_cases horizontal : firstX = secondX
  · have vertical : firstY ≠ secondY := by
      intro vertical
      apply different
      exact Prod.ext horizontal vertical
    rcases lt_or_gt_of_ne vertical with
      forward | backward
    · exact Or.inr (Or.inr (Or.inl forward))
    · exact Or.inr (Or.inr (Or.inr backward))
  · rcases lt_or_gt_of_ne horizontal with
      forward | backward
    · exact Or.inl forward
    · exact Or.inr (Or.inl backward)

/-- Scaling separated rectangles leaves room for a coordinate-radius box
around a scaled singleton whenever the radius is smaller than the scale. -/
theorem ClosedGridRectanglesSeparated.scale_left_point_radius
    {firstLower firstUpper center : Cell}
    {factor radius : Nat}
    (separated :
      ClosedGridRectanglesSeparated
        firstLower firstUpper center center)
    (factorPositive : 0 < factor)
    (radiusLt : radius < factor) :
    ClosedGridRectanglesSeparated
      (Cell.scale factor firstLower)
      (Cell.scale factor firstUpper)
      (coordinateRadiusLower radius
        (Cell.scale factor center))
      (coordinateRadiusUpper radius
        (Cell.scale factor center)) := by
  rcases firstLower with ⟨firstLowerX, firstLowerY⟩
  rcases firstUpper with ⟨firstUpperX, firstUpperY⟩
  rcases center with ⟨centerX, centerY⟩
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
    have gap : firstUpperX + 1 ≤ centerX := by
      omega
    have scaled :=
      mul_le_mul_of_nonneg_left gap factorNonnegativeInt
    rw [mul_add] at scaled
    omega
  · right
    left
    have gap : centerX + 1 ≤ firstLowerX := by
      omega
    have scaled :=
      mul_le_mul_of_nonneg_left gap factorNonnegativeInt
    rw [mul_add] at scaled
    omega
  · right
    right
    left
    have gap : firstUpperY + 1 ≤ centerY := by
      omega
    have scaled :=
      mul_le_mul_of_nonneg_left gap factorNonnegativeInt
    rw [mul_add] at scaled
    omega
  · right
    right
    right
    have gap : centerY + 1 ≤ firstLowerY := by
      omega
    have scaled :=
      mul_le_mul_of_nonneg_left gap factorNonnegativeInt
    rw [mul_add] at scaled
    omega

/-- A finite route that avoids one integral source point remains strictly
separated, after scaling, from every route in a smaller coordinate-radius
neighborhood of the scaled point. -/
theorem routesStrictlyAvoidEachOther_scalePolyline_pointNeighborhood
    {source nearby : List Cell}
    {center : Cell}
    {factor radius : Nat}
    (factorPositive : 0 < factor)
    (radiusLt : radius < factor)
    (sourcePointsAvoid :
      ∀ point ∈ source, point ≠ center)
    (sourceSegmentsAvoid :
      ∀ segment ∈ gridPolylineSegments source,
        segment.IsAxisAligned →
          ¬segment.Contains center)
    (nearbyBounded :
      ∀ point ∈ nearby,
        WithinCoordinateRadius radius
          (Cell.scale factor center) point) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther
      (scalePolyline factor source) nearby := by
  open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing in
    unfold RoutesStrictlyAvoidEachOther
  have factorPositiveInt :
      (0 : Int) < factor := by
    exact_mod_cast factorPositive
  have factorNonnegativeInt :
      (0 : Int) ≤ factor :=
    factorPositiveInt.le
  rw [gridPolylineSegments_scalePolyline]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro scaledSourceSegment scaledSourceMember
      nearbySegment nearbySegmentMember
    rcases List.mem_map.mp scaledSourceMember with
      ⟨sourceSegment, sourceSegmentMember, rfl⟩
    by_cases aligned : sourceSegment.IsAxisAligned
    · have separated :=
        (sourceSegment.coordinateRectangle_separated_point
          aligned
          (sourceSegmentsAvoid sourceSegment
            sourceSegmentMember aligned))
          |>.scale_left_point_radius
            factorPositive radiusLt
      have nearbyEndpoints :=
        gridPolylineSegments_endpoints_mem nearbySegmentMember
      exact
        not_interiorsMeet_of_inClosedGridRectangles_of_separated
          (sourceSegment.start_in_coordinateRectangle.scale
            factorNonnegativeInt)
          (sourceSegment.finish_in_coordinateRectangle.scale
            factorNonnegativeInt)
          (inClosedGridRectangle_coordinateRadius
            (nearbyBounded _ nearbyEndpoints.1))
          (inClosedGridRectangle_coordinateRadius
            (nearbyBounded _ nearbyEndpoints.2))
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
      (closedGridSingletons_separated_of_ne
        (sourcePointsAvoid sourcePoint sourcePointMember))
        |>.scale_left_point_radius
          factorPositive radiusLt
    have nearbyEndpoints :=
      gridPolylineSegments_endpoints_mem nearbySegmentMember
    exact
      not_interiorContains_of_inClosedGridRectangles_of_separated
        (by
          exact
            ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩)
        (inClosedGridRectangle_coordinateRadius
          (nearbyBounded _ nearbyEndpoints.1))
        (inClosedGridRectangle_coordinateRadius
          (nearbyBounded _ nearbyEndpoints.2))
        separated
  · intro nearbyPoint nearbyPointMember
      scaledSourceSegment scaledSourceMember
    rcases List.mem_map.mp scaledSourceMember with
      ⟨sourceSegment, sourceSegmentMember, rfl⟩
    by_cases aligned : sourceSegment.IsAxisAligned
    · have separated :=
        (sourceSegment.coordinateRectangle_separated_point
          aligned
          (sourceSegmentsAvoid sourceSegment
            sourceSegmentMember aligned))
          |>.scale_left_point_radius
            factorPositive radiusLt
      exact
        not_interiorContains_of_inClosedGridRectangles_of_separated
          (inClosedGridRectangle_coordinateRadius
            (nearbyBounded _ nearbyPointMember))
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
      (closedGridSingletons_separated_of_ne
        (sourcePointsAvoid sourcePoint sourcePointMember))
        |>.scale_left_point_radius
          factorPositive radiusLt
    exact
      ne_of_inClosedGridRectangles_of_separated
        (by
          exact
            ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩)
        (inClosedGridRectangle_coordinateRadius
          (nearbyBounded _ nearbyPointMember))
        separated

end LeanTrominoes
