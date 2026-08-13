/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineBoundingBox
import LeanTrominoes.OrthogonalPolylineLoopErasure
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

/-- A simple route's tail neither lists the discarded head nor contains it
anywhere along a surviving tail segment. -/
theorem LocalIncidenceDrawing.RouteIsSimple.tail_avoids_head
    {route : List Cell} {head : Cell}
    (simple : LocalIncidenceDrawing.RouteIsSimple route)
    (headLookup : route.head? = some head) :
    (∀ point ∈ route.tail, point ≠ head) ∧
      ∀ segment ∈ gridPolylineSegments route.tail,
        segment.IsAxisAligned →
          ¬segment.Contains head := by
  have headMember : head ∈ route :=
    List.mem_of_mem_head? headLookup
  have headFresh : head ∉ route.tail :=
    AxisDirection.headNotInTail_of_nodup simple.1
      head headLookup
  constructor
  · intro point pointMember pointEqual
    subst point
    exact headFresh pointMember
  · intro segment segmentMember _segmentAligned contains
    rcases
        GridSegment.interiorContains_or_eq_start_or_eq_finish_of_contains
          contains with
      interior | endpoint
    · exact
        simple.2.1 head headMember segment
          (gridPolylineSegments_tail_subset route segmentMember)
          interior
    · have endpoints :=
        gridPolylineSegments_endpoints_mem segmentMember
      rcases endpoint with atStart | atFinish
      · exact headFresh (atStart.symm ▸ endpoints.1)
      · exact headFresh (atFinish.symm ▸ endpoints.2)

/-- If two ordinarily separated routes have different heads and the first
head is not the second tail, then the whole second route avoids the first
head, both at its listed points and along every segment.  This packages the
endpoint bookkeeping needed to apply a scaled point-neighborhood theorem at
one route's clause-side endpoint. -/
theorem
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther.second_avoids_first_head_of_endpoints_ne
    {first second : List Cell}
    {firstHead secondHead secondLast : Cell}
    (avoid :
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
        first second)
    (firstHeadLookup : first.head? = some firstHead)
    (secondHeadLookup : second.head? = some secondHead)
    (secondLastLookup : second.getLast? = some secondLast)
    (headsDifferent : firstHead ≠ secondHead)
    (firstHeadDifferentSecondLast : firstHead ≠ secondLast) :
    (∀ point ∈ second, point ≠ firstHead) ∧
      ∀ segment ∈ gridPolylineSegments second,
        ¬segment.Contains firstHead := by
  have firstHeadMember : firstHead ∈ first :=
    List.mem_of_mem_head? firstHeadLookup
  have pointsAvoid : ∀ point ∈ second, point ≠ firstHead := by
    intro point pointMember pointEqual
    subst point
    rcases List.mem_iff_get.mp firstHeadMember with
      ⟨firstIndex, firstIndexed⟩
    rcases List.mem_iff_get.mp pointMember with
      ⟨secondIndex, secondIndexed⟩
    have indexedEqual :
        first.get firstIndex = second.get secondIndex := by
      rw [firstIndexed, secondIndexed]
    have endpoints :=
      avoid.2.2.2 firstIndex secondIndex indexedEqual
    rw [firstIndexed, secondIndexed] at endpoints
    rcases endpoints.2 with secondHead | secondLast
    · exact headsDifferent
        (Option.some.inj (secondHead.symm.trans secondHeadLookup))
    · exact firstHeadDifferentSecondLast
        (Option.some.inj (secondLast.symm.trans secondLastLookup))
  refine ⟨pointsAvoid, ?_⟩
  intro segment segmentMember contains
  rcases
      GridSegment.interiorContains_or_eq_start_or_eq_finish_of_contains
        contains with
    interior | endpoint
  · rcases List.mem_iff_get.mp firstHeadMember with
      ⟨firstIndex, firstIndexed⟩
    rcases List.mem_iff_get.mp segmentMember with
      ⟨secondSegmentIndex, secondSegmentIndexed⟩
    have interiorAvoid := avoid.2.1 firstIndex secondSegmentIndex
    rw [firstIndexed, secondSegmentIndexed] at interiorAvoid
    exact interiorAvoid interior
  · have segmentEndpoints :=
      gridPolylineSegments_endpoints_mem segmentMember
    rcases endpoint with atStart | atFinish
    · exact pointsAvoid segment.start segmentEndpoints.1 atStart.symm
    · exact pointsAvoid segment.finish segmentEndpoints.2 atFinish.symm

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

/-- Scaling two separated integral rectangles leaves room to expand both by
the same coordinate radius when twice that radius is smaller than the scale.
This local variant keeps the point-neighborhood infrastructure independent
of the retained-ray rasterization modules. -/
theorem ClosedGridRectanglesSeparated.scale_both_coordinateRadius'
    {firstLower firstUpper secondLower secondUpper : Cell}
    {factor radius : Nat}
    (separated :
      ClosedGridRectanglesSeparated
        firstLower firstUpper secondLower secondUpper)
    (factorPositive : 0 < factor)
    (twiceRadiusLt : 2 * radius < factor) :
    ClosedGridRectanglesSeparated
      (coordinateRadiusLower radius
        (Cell.scale factor firstLower))
      (coordinateRadiusUpper radius
        (Cell.scale factor firstUpper))
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
  have twiceRadiusLtInt :
      2 * (radius : Int) < factor := by
    exact_mod_cast twiceRadiusLt
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

/-- Routes in equal-radius neighborhoods of two distinct integral centers
are contact-free after a common scale with more than twice the radius of
clearance. -/
theorem
    routesStrictlyAvoidEachOther_of_distinct_scaledCoordinateNeighborhoods
    {first second : List Cell}
    {firstCenter secondCenter : Cell}
    {factor radius : Nat}
    (centersDifferent : firstCenter ≠ secondCenter)
    (factorPositive : 0 < factor)
    (clearance : 2 * radius < factor)
    (firstBounded :
      ∀ point ∈ first,
        WithinCoordinateRadius radius
          (Cell.scale factor firstCenter) point)
    (secondBounded :
      ∀ point ∈ second,
        WithinCoordinateRadius radius
          (Cell.scale factor secondCenter) point) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther
      first second := by
  apply routesStrictlyAvoidEachOther_of_inSeparatedClosedGridRectangles
  · intro point pointMember
    exact inClosedGridRectangle_coordinateRadius
      (firstBounded point pointMember)
  · intro point pointMember
    exact inClosedGridRectangle_coordinateRadius
      (secondBounded point pointMember)
  · exact
      (closedGridSingletons_separated_of_ne centersDifferent)
        |>.scale_both_coordinateRadius'
          factorPositive clearance

/-- A common integral offset of both scaled neighborhood centers does not
affect the strict-separation guarantee. -/
theorem
    routesStrictlyAvoidEachOther_of_distinct_offsetScaledCoordinateNeighborhoods
    {first second : List Cell}
    {firstCenter secondCenter offset : Cell}
    {factor radius : Nat}
    (centersDifferent : firstCenter ≠ secondCenter)
    (factorPositive : 0 < factor)
    (clearance : 2 * radius < factor)
    (firstBounded :
      ∀ point ∈ first,
        WithinCoordinateRadius radius
          (Cell.add (Cell.scale factor firstCenter) offset) point)
    (secondBounded :
      ∀ point ∈ second,
        WithinCoordinateRadius radius
          (Cell.add (Cell.scale factor secondCenter) offset) point) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther
      first second := by
  apply routesStrictlyAvoidEachOther_of_inSeparatedClosedGridRectangles
  · intro point pointMember
    exact inClosedGridRectangle_coordinateRadius
      (firstBounded point pointMember)
  · intro point pointMember
    exact inClosedGridRectangle_coordinateRadius
      (secondBounded point pointMember)
  · have separated :=
      (closedGridSingletons_separated_of_ne centersDifferent)
        |>.scale_both_coordinateRadius'
          factorPositive clearance
    rcases firstCenter with ⟨firstX, firstY⟩
    rcases secondCenter with ⟨secondX, secondY⟩
    rcases offset with ⟨offsetX, offsetY⟩
    simp only [ClosedGridRectanglesSeparated,
      coordinateRadiusLower, coordinateRadiusUpper,
      Cell.scale, Cell.add] at separated ⊢
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

/-- The point-neighborhood clearance theorem is invariant under a common
translation of the scaled source route and the neighborhood center. -/
theorem
    routesStrictlyAvoidEachOther_translateScalePolyline_pointNeighborhood
    {source nearby : List Cell}
    {center offset : Cell}
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
          (Cell.add offset (Cell.scale factor center)) point) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther
      (PeriodicOrthocrossing.translatePolyline offset
        (scalePolyline factor source))
      nearby := by
  let inverse : Cell := (-offset.1, -offset.2)
  let unshiftedNearby :=
    PeriodicOrthocrossing.translatePolyline inverse nearby
  have unshiftedBounded :
      ∀ point ∈ unshiftedNearby,
        WithinCoordinateRadius radius
          (Cell.scale factor center) point := by
    intro point pointMember
    rcases List.mem_map.mp pointMember with
      ⟨original, originalMember, rfl⟩
    have translated :=
      (nearbyBounded original originalMember).translate inverse
    simpa [inverse, Cell.add] using translated
  have base :=
    routesStrictlyAvoidEachOther_scalePolyline_pointNeighborhood
      factorPositive radiusLt sourcePointsAvoid
      sourceSegmentsAvoid unshiftedBounded
  have translated := base.translatePolyline offset
  have restoreNearby :
      PeriodicOrthocrossing.translatePolyline offset unshiftedNearby =
        nearby := by
    simp [unshiftedNearby, inverse,
      PeriodicOrthocrossing.translatePolyline,
      List.map_map, Function.comp_def, Cell.add]
  simpa [restoreNearby] using translated

end LeanTrominoes
