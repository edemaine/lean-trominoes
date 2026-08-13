/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineLinearSeparation
import LeanTrominoes.ScaledSegmentNeighborhoodSeparation

/-!
# Mixed separation from a scaled route neighborhood

A diagonal reference segment has two useful separating axes.  A source
piece can miss its endpoint rectangle longitudinally, or it can lie
strictly on one side of the segment's supporting line.  Different pieces
of one source route may need different choices.

This file packages that piecewise separating-axis argument.  It is the
generic bridge from finite unscaled certificates to a fixed-size route
inside both a coordinate rectangle and a transverse band around the
scaled reference.
-/

namespace LeanTrominoes

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- One point clears a reference corridor either through rectangle
separation or through either strict side of a supporting line. -/
def PointSeparatesRectangleOrLine
    (point referenceLower referenceUpper referenceCenter normal : Cell) :
    Prop :=
  ClosedGridRectanglesSeparated
      point point referenceLower referenceUpper ∨
    Cell.linearValue normal point <
        Cell.linearValue normal referenceCenter ∨
      Cell.linearValue normal referenceCenter <
        Cell.linearValue normal point

instance
    (point referenceLower referenceUpper referenceCenter normal : Cell) :
    Decidable
      (PointSeparatesRectangleOrLine
        point referenceLower referenceUpper referenceCenter normal) := by
  unfold PointSeparatesRectangleOrLine
  infer_instance

/-- One axis-aligned segment clears a reference corridor either through
rectangle separation or by putting both endpoints strictly on the same
side of a supporting line. -/
def SegmentSeparatesRectangleOrLine
    (segment : GridSegment)
    (referenceLower referenceUpper referenceCenter normal : Cell) :
    Prop :=
  ClosedGridRectanglesSeparated
      segment.coordinateLower segment.coordinateUpper
      referenceLower referenceUpper ∨
    (Cell.linearValue normal segment.start <
          Cell.linearValue normal referenceCenter ∧
        Cell.linearValue normal segment.finish <
          Cell.linearValue normal referenceCenter) ∨
      (Cell.linearValue normal referenceCenter <
          Cell.linearValue normal segment.start ∧
        Cell.linearValue normal referenceCenter <
          Cell.linearValue normal segment.finish)

instance
    (segment : GridSegment)
    (referenceLower referenceUpper referenceCenter normal : Cell) :
    Decidable
      (SegmentSeparatesRectangleOrLine
        segment referenceLower referenceUpper referenceCenter normal) := by
  unfold SegmentSeparatesRectangleOrLine
  infer_instance

/-- Piecewise rectangle-or-linear separation survives scaling and clears
any route in the corresponding rectangle and transverse neighborhoods. -/
theorem
    routesStrictlyAvoidEachOther_scalePolyline_rectangleOrLinearNeighborhood
    {source nearby : List Cell}
    {referenceLower referenceUpper referenceCenter normal : Cell}
    {factor rectangleRadius linearRadius : Nat}
    (factorPositive : 0 < factor)
    (rectangleRadiusLt : rectangleRadius < factor)
    (linearRadiusLt : linearRadius < factor)
    (sourcePointSeparated :
      ∀ point ∈ source,
        PointSeparatesRectangleOrLine
          point referenceLower referenceUpper referenceCenter normal)
    (sourceSegmentSeparated :
      ∀ segment ∈ gridPolylineSegments source,
        segment.IsAxisAligned →
          SegmentSeparatesRectangleOrLine
            segment referenceLower referenceUpper referenceCenter normal)
    (nearbyRectangleBounded :
      ∀ point ∈ nearby,
        InClosedGridRectangle
          (coordinateRadiusLower rectangleRadius
            (Cell.scale factor referenceLower))
          (coordinateRadiusUpper rectangleRadius
            (Cell.scale factor referenceUpper))
          point)
    (nearbyLinearBounded :
      ∀ point ∈ nearby,
        Cell.linearValue normal
              (Cell.scale factor referenceCenter) -
            linearRadius ≤
          Cell.linearValue normal point ∧
        Cell.linearValue normal point ≤
          Cell.linearValue normal
              (Cell.scale factor referenceCenter) +
            linearRadius) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline factor source) nearby := by
  have factorPositiveInt : (0 : Int) < factor := by
    exact_mod_cast factorPositive
  have factorNonnegativeInt : (0 : Int) ≤ factor :=
    factorPositiveInt.le
  have linearRadiusLtInt : (linearRadius : Int) < factor := by
    exact_mod_cast linearRadiusLt
  have linearValueScale (point : Cell) :
      Cell.linearValue normal (Cell.scale factor point) =
        factor * Cell.linearValue normal point := by
    rcases normal with ⟨normalX, normalY⟩
    rcases point with ⟨pointX, pointY⟩
    simp [Cell.linearValue, Cell.scale]
    ring
  have scaledBelow
      (point : Cell)
      (below :
        Cell.linearValue normal point <
          Cell.linearValue normal referenceCenter) :
      Cell.linearValue normal (Cell.scale factor point) ≤
        Cell.linearValue normal
            (Cell.scale factor referenceCenter) -
          factor := by
    have integralGap :
        Cell.linearValue normal point + 1 ≤
          Cell.linearValue normal referenceCenter := by
      omega
    have scaledGap :=
      mul_le_mul_of_nonneg_left integralGap factorNonnegativeInt
    rw [linearValueScale, linearValueScale]
    rw [mul_add] at scaledGap
    omega
  have scaledAbove
      (point : Cell)
      (above :
        Cell.linearValue normal referenceCenter <
          Cell.linearValue normal point) :
      Cell.linearValue normal
            (Cell.scale factor referenceCenter) +
          factor ≤
        Cell.linearValue normal (Cell.scale factor point) := by
    have integralGap :
        Cell.linearValue normal referenceCenter + 1 ≤
          Cell.linearValue normal point := by
      omega
    have scaledGap :=
      mul_le_mul_of_nonneg_left integralGap factorNonnegativeInt
    rw [linearValueScale, linearValueScale]
    rw [mul_add] at scaledGap
    omega
  have nearbyAboveLower
      (point : Cell) (pointMember : point ∈ nearby) :
      Cell.linearValue normal
            (Cell.scale factor referenceCenter) -
          factor <
        Cell.linearValue normal point := by
    have lower := (nearbyLinearBounded point pointMember).1
    omega
  have nearbyBelowUpper
      (point : Cell) (pointMember : point ∈ nearby) :
      Cell.linearValue normal point <
        Cell.linearValue normal
            (Cell.scale factor referenceCenter) +
          factor := by
    have upper := (nearbyLinearBounded point pointMember).2
    omega
  unfold RoutesStrictlyAvoidEachOther
  rw [gridPolylineSegments_scalePolyline]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro scaledSourceSegment scaledSourceMember
      nearbySegment nearbySegmentMember
    rcases List.mem_map.mp scaledSourceMember with
      ⟨sourceSegment, sourceSegmentMember, rfl⟩
    by_cases aligned : sourceSegment.IsAxisAligned
    · rcases
          sourceSegmentSeparated
            sourceSegment sourceSegmentMember aligned with
        rectangle | below | above
      · have separated :=
          rectangle.scale_left_rectangle_radius
            factorPositive rectangleRadiusLt
        have nearbyEndpoints :=
          gridPolylineSegments_endpoints_mem nearbySegmentMember
        exact
          not_interiorsMeet_of_inClosedGridRectangles_of_separated
            (sourceSegment.start_in_coordinateRectangle.scale
              factorNonnegativeInt)
            (sourceSegment.finish_in_coordinateRectangle.scale
              factorNonnegativeInt)
            (nearbyRectangleBounded _ nearbyEndpoints.1)
            (nearbyRectangleBounded _ nearbyEndpoints.2)
            separated
      · have nearbyEndpoints :=
          gridPolylineSegments_endpoints_mem nearbySegmentMember
        exact
          Cell.not_interiorsMeet_of_linear_separated
            normal
            (Cell.linearValue normal
                (Cell.scale factor referenceCenter) -
              factor)
            (scaledBelow sourceSegment.start below.1)
            (scaledBelow sourceSegment.finish below.2)
            (nearbyAboveLower _ nearbyEndpoints.1)
            (nearbyAboveLower _ nearbyEndpoints.2)
      · have nearbyEndpoints :=
          gridPolylineSegments_endpoints_mem nearbySegmentMember
        intro meet
        exact
          (Cell.not_interiorsMeet_of_linear_separated
            normal
            (Cell.linearValue normal
                (Cell.scale factor referenceCenter) +
              linearRadius)
            (nearbyLinearBounded _ nearbyEndpoints.1).2
            (nearbyLinearBounded _ nearbyEndpoints.2).2
            (lt_of_lt_of_le
              (by omega)
              (scaledAbove sourceSegment.start above.1))
            (lt_of_lt_of_le
              (by omega)
              (scaledAbove sourceSegment.finish above.2)))
            ((GridSegment.interiorsMeet_comm _ _).mpr meet)
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
    rcases sourcePointSeparated sourcePoint sourcePointMember with
      rectangle | below | above
    · have separated :=
        rectangle.scale_left_rectangle_radius
          factorPositive rectangleRadiusLt
      have nearbyEndpoints :=
        gridPolylineSegments_endpoints_mem nearbySegmentMember
      exact
        not_interiorContains_of_inClosedGridRectangles_of_separated
          (by exact ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩)
          (nearbyRectangleBounded _ nearbyEndpoints.1)
          (nearbyRectangleBounded _ nearbyEndpoints.2)
          separated
    · have nearbyEndpoints :=
        gridPolylineSegments_endpoints_mem nearbySegmentMember
      intro interior
      have contained :=
        GridSegment.contains_of_interiorContains interior
      have nearbyValue :=
        Cell.linearValue_gt_of_segment_contains
          normal
          (Cell.linearValue normal
              (Cell.scale factor referenceCenter) -
            factor)
          (nearbyAboveLower _ nearbyEndpoints.1)
          (nearbyAboveLower _ nearbyEndpoints.2)
          contained
      exact
        (not_lt_of_ge (scaledBelow sourcePoint below))
          nearbyValue
    · have nearbyEndpoints :=
        gridPolylineSegments_endpoints_mem nearbySegmentMember
      intro interior
      have contained :=
        GridSegment.contains_of_interiorContains interior
      have nearbyValue :=
        Cell.linearValue_le_of_segment_contains
          normal
          (Cell.linearValue normal
              (Cell.scale factor referenceCenter) +
            linearRadius)
          (nearbyLinearBounded _ nearbyEndpoints.1).2
          (nearbyLinearBounded _ nearbyEndpoints.2).2
          contained
      have sourceValue :
          Cell.linearValue normal
                (Cell.scale factor referenceCenter) +
              linearRadius <
            Cell.linearValue normal
              (Cell.scale factor sourcePoint) :=
        lt_of_lt_of_le
          (by omega)
          (scaledAbove sourcePoint above)
      exact (not_lt_of_ge nearbyValue) sourceValue
  · intro nearbyPoint nearbyPointMember
      scaledSourceSegment scaledSourceMember
    rcases List.mem_map.mp scaledSourceMember with
      ⟨sourceSegment, sourceSegmentMember, rfl⟩
    by_cases aligned : sourceSegment.IsAxisAligned
    · rcases
          sourceSegmentSeparated
            sourceSegment sourceSegmentMember aligned with
        rectangle | below | above
      · have separated :=
          rectangle.scale_left_rectangle_radius
            factorPositive rectangleRadiusLt
        exact
          not_interiorContains_of_inClosedGridRectangles_of_separated
            (nearbyRectangleBounded _ nearbyPointMember)
            (sourceSegment.start_in_coordinateRectangle.scale
              factorNonnegativeInt)
            (sourceSegment.finish_in_coordinateRectangle.scale
              factorNonnegativeInt)
            separated.symm
      · intro interior
        have contained :=
          GridSegment.contains_of_interiorContains interior
        have sourceValue :=
          Cell.linearValue_le_of_segment_contains
            normal
            (Cell.linearValue normal
                (Cell.scale factor referenceCenter) -
              factor)
            (scaledBelow sourceSegment.start below.1)
            (scaledBelow sourceSegment.finish below.2)
            contained
        exact
          (not_lt_of_ge sourceValue)
            (nearbyAboveLower nearbyPoint nearbyPointMember)
      · intro interior
        have contained :=
          GridSegment.contains_of_interiorContains interior
        have sourceValue :=
          Cell.linearValue_gt_of_segment_contains
            normal
            (Cell.linearValue normal
                (Cell.scale factor referenceCenter) +
              linearRadius)
            (lt_of_lt_of_le
              (by omega)
              (scaledAbove sourceSegment.start above.1))
            (lt_of_lt_of_le
              (by omega)
              (scaledAbove sourceSegment.finish above.2))
            contained
        exact
          (not_lt_of_ge
            (nearbyLinearBounded nearbyPoint nearbyPointMember).2)
            sourceValue
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
    rcases sourcePointSeparated sourcePoint sourcePointMember with
      rectangle | below | above
    · have separated :=
        rectangle.scale_left_rectangle_radius
          factorPositive rectangleRadiusLt
      exact
        ne_of_inClosedGridRectangles_of_separated
          (by exact ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩)
          (nearbyRectangleBounded _ nearbyPointMember)
          separated
    · intro equal
      subst nearbyPoint
      exact
        (not_lt_of_ge (scaledBelow sourcePoint below))
          (nearbyAboveLower
            (Cell.scale factor sourcePoint)
            nearbyPointMember)
    · intro equal
      subst nearbyPoint
      have sourceValue :
          Cell.linearValue normal
                (Cell.scale factor referenceCenter) +
              linearRadius <
            Cell.linearValue normal
              (Cell.scale factor sourcePoint) :=
        lt_of_lt_of_le
          (by omega)
          (scaledAbove sourcePoint above)
      exact
        (not_lt_of_ge
          (nearbyLinearBounded
            (Cell.scale factor sourcePoint)
            nearbyPointMember).2)
          sourceValue

end LeanTrominoes
