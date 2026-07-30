import LeanTrominoes.RetainedTerminalCheckpointRasterization

/-!
# Quantitative separation of retained-ray rasterizations

Rasterization replaces each retained straight segment by an orthogonal
staircase within coordinate radius nine of exact checkpoints on that segment.
This file turns the checkpoint statement into closed-rectangle bounds and
proves that a source segment can be recovered from every segment of a
rasterized polyline.

These are the quantitative ingredients for lifting robust separation of
source segments through scaling, retained-ray rasterization, and unit
subdivision.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A checkpoint between the endpoints of a retained segment lies in the
segment's closed coordinate rectangle. -/
theorem retainedSegmentCheckpoint_in_coordinateRectangle
    (segment : GridSegment)
    (primitive : Cell)
    (length index : Nat)
    (vector :
      Cell.sub segment.finish segment.start =
        Cell.scale length primitive)
    (indexBound : index ≤ length) :
    InClosedGridRectangle
      segment.coordinateLower segment.coordinateUpper
      (Cell.add segment.start
        (Cell.scale index primitive)) := by
  rcases segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases primitive with ⟨primitiveX, primitiveY⟩
  have indexNonnegative : (0 : Int) ≤ index := by
    exact_mod_cast Nat.zero_le index
  have lengthNonnegative : (0 : Int) ≤ length := by
    exact_mod_cast Nat.zero_le length
  have indexBoundInt : (index : Int) ≤ length := by
    exact_mod_cast indexBound
  have horizontalForward :
      0 ≤ primitiveX →
        startX ≤ startX + (index : Int) * primitiveX ∧
          startX + (index : Int) * primitiveX ≤ finishX := by
    intro primitiveNonnegative
    have firstProduct :
        0 ≤ (index : Int) * primitiveX :=
      mul_nonneg indexNonnegative primitiveNonnegative
    have secondProduct :
        (index : Int) * primitiveX ≤
          (length : Int) * primitiveX :=
      mul_le_mul_of_nonneg_right
        indexBoundInt primitiveNonnegative
    simp only [Cell.sub, Cell.scale, Prod.mk.injEq] at vector
    omega
  have horizontalBackward :
      primitiveX ≤ 0 →
        finishX ≤ startX + (index : Int) * primitiveX ∧
          startX + (index : Int) * primitiveX ≤ startX := by
    intro primitiveNonpositive
    have firstProduct :
        (index : Int) * primitiveX ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos
        indexNonnegative primitiveNonpositive
    have secondProduct :
        (length : Int) * primitiveX ≤
          (index : Int) * primitiveX :=
      mul_le_mul_of_nonpos_right
        indexBoundInt primitiveNonpositive
    simp only [Cell.sub, Cell.scale, Prod.mk.injEq] at vector
    omega
  have verticalForward :
      0 ≤ primitiveY →
        startY ≤ startY + (index : Int) * primitiveY ∧
          startY + (index : Int) * primitiveY ≤ finishY := by
    intro primitiveNonnegative
    have firstProduct :
        0 ≤ (index : Int) * primitiveY :=
      mul_nonneg indexNonnegative primitiveNonnegative
    have secondProduct :
        (index : Int) * primitiveY ≤
          (length : Int) * primitiveY :=
      mul_le_mul_of_nonneg_right
        indexBoundInt primitiveNonnegative
    simp only [Cell.sub, Cell.scale, Prod.mk.injEq] at vector
    omega
  have verticalBackward :
      primitiveY ≤ 0 →
        finishY ≤ startY + (index : Int) * primitiveY ∧
          startY + (index : Int) * primitiveY ≤ startY := by
    intro primitiveNonpositive
    have firstProduct :
        (index : Int) * primitiveY ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos
        indexNonnegative primitiveNonpositive
    have secondProduct :
        (length : Int) * primitiveY ≤
          (index : Int) * primitiveY :=
      mul_le_mul_of_nonpos_right
        indexBoundInt primitiveNonpositive
    simp only [Cell.sub, Cell.scale, Prod.mk.injEq] at vector
    omega
  simp only [InClosedGridRectangle,
    GridSegment.coordinateLower,
    GridSegment.coordinateUpper,
    Cell.add, Cell.scale]
  constructor
  · by_cases nonnegative : 0 ≤ primitiveX
    · have bounds := horizontalForward nonnegative
      simp [min_def]
      omega
    · have bounds := horizontalBackward (le_of_not_ge nonnegative)
      simp [min_def]
      omega
  · constructor
    · by_cases nonnegative : 0 ≤ primitiveX
      · have bounds := horizontalForward nonnegative
        simp [max_def]
        omega
      · have bounds := horizontalBackward (le_of_not_ge nonnegative)
        simp [max_def]
        omega
    · constructor
      · by_cases nonnegative : 0 ≤ primitiveY
        · have bounds := verticalForward nonnegative
          simp [min_def]
          omega
        · have bounds := verticalBackward (le_of_not_ge nonnegative)
          simp [min_def]
          omega
      · by_cases nonnegative : 0 ≤ primitiveY
        · have bounds := verticalForward nonnegative
          simp [max_def]
          omega
        · have bounds := verticalBackward (le_of_not_ge nonnegative)
          simp [max_def]
          omega

/-- Every point in a retained segment's radius-nine raster corridor lies in
the radius-nine expansion of its endpoint rectangle. -/
theorem inExpandedCoordinateRectangle_of_inRetainedSegmentRasterCorridor
    {segment : GridSegment} {point : Cell}
    (corridor :
      InRetainedSegmentRasterCorridor segment point) :
    InClosedGridRectangle
      (coordinateRadiusLower 9 segment.coordinateLower)
      (coordinateRadiusUpper 9 segment.coordinateUpper)
      point := by
  rcases corridor with
    ⟨primitive, length, index, _lengthPositive,
      vector, indexBound, nearby⟩
  have checkpointBound :=
    retainedSegmentCheckpoint_in_coordinateRectangle
      segment primitive length index vector indexBound
  have nearbyBounds := nearby.coordinate_bounds
  rcases segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases primitive with ⟨primitiveX, primitiveY⟩
  rcases point with ⟨pointX, pointY⟩
  simp only [InClosedGridRectangle,
    GridSegment.coordinateLower,
    GridSegment.coordinateUpper,
    Cell.add, Cell.scale] at checkpointBound
  simp only [Cell.add, Cell.scale] at nearbyBounds
  simp only [coordinateRadiusLower, coordinateRadiusUpper,
    GridSegment.coordinateLower,
    GridSegment.coordinateUpper,
    InClosedGridRectangle]
  omega

/-- Every segment of a rasterized polyline comes from the rasterization of
one source segment. -/
theorem
    exists_sourceSegment_of_mem_rasterizeRetainedPolyline_segments
    {points : List Cell}
    {rasterSegment : GridSegment}
    (rasterMember :
      rasterSegment ∈
        gridPolylineSegments
          (rasterizeRetainedPolyline points)) :
    ∃ sourceSegment ∈ gridPolylineSegments points,
      rasterSegment ∈
        gridPolylineSegments
          (rasterizeRetainedSegment sourceSegment) := by
  induction points using List.twoStepInduction with
  | nil =>
      simp [gridPolylineSegments] at rasterMember
  | singleton only =>
      simp [gridPolylineSegments] at rasterMember
  | cons_cons first second rest _ tailInduction =>
      rw [rasterizeRetainedPolyline_cons_cons,
        gridPolylineSegments_joinAtEndpoint
          (rasterizeRetainedSegment_getLast?
            (GridSegment.mk first second))
          (by
            rw [rasterizeRetainedPolyline_head?]
            rfl),
        List.mem_append] at rasterMember
      rcases rasterMember with firstMember | tailMember
      · exact
          ⟨GridSegment.mk first second,
            by simp [gridPolylineSegments],
            firstMember⟩
      · rcases tailInduction second tailMember with
          ⟨sourceSegment, sourceMember, member⟩
        exact
          ⟨sourceSegment,
            by
              simp only [gridPolylineSegments, List.mem_cons]
              exact Or.inr sourceMember,
            member⟩

/-- Every point of a unit-subdivided retained rasterization lies in the
radius-nine expanded endpoint rectangle of one source segment. -/
theorem
    unitSubdividedRasterizeRetainedPolyline_point_in_sourceRectangle
    {points : List Cell}
    (retained : RetainedRayPolyline points)
    (length : 2 ≤ points.length)
    {point : Cell}
    (pointMember :
      point ∈
        AxisDirection.unitSubdividePolyline
          (rasterizeRetainedPolyline points)) :
    ∃ sourceSegment ∈ gridPolylineSegments points,
      InClosedGridRectangle
        (coordinateRadiusLower 9 sourceSegment.coordinateLower)
        (coordinateRadiusUpper 9 sourceSegment.coordinateUpper)
        point := by
  have rasterOrthogonal :=
    rasterizeRetainedPolyline_orthogonal retained
  rcases
      AxisDirection.unitSubdividePolyline_mem_original_or_segmentInterior
        rasterOrthogonal pointMember with
    rawMember | ⟨rasterSegment, rasterMember, pointInterior⟩
  · rcases
        rasterizeRetainedPolyline_point_in_corridor
          retained length rawMember with
      ⟨sourceSegment, sourceMember, corridor⟩
    exact
      ⟨sourceSegment, sourceMember,
        inExpandedCoordinateRectangle_of_inRetainedSegmentRasterCorridor
          corridor⟩
  · rcases
        exists_sourceSegment_of_mem_rasterizeRetainedPolyline_segments
          rasterMember with
      ⟨sourceSegment, sourceMember, sourceRasterMember⟩
    have endpoints :=
      gridPolylineSegments_endpoints_mem sourceRasterMember
    have startBound :=
      inExpandedCoordinateRectangle_of_inRetainedSegmentRasterCorridor
        (rasterizeRetainedSegment_point_in_corridor
          sourceSegment
          (retained sourceSegment sourceMember)
          endpoints.1)
    have finishBound :=
      inExpandedCoordinateRectangle_of_inRetainedSegmentRasterCorridor
        (rasterizeRetainedSegment_point_in_corridor
          sourceSegment
          (retained sourceSegment sourceMember)
          endpoints.2)
    exact
      ⟨sourceSegment, sourceMember,
        inClosedGridRectangle_of_segment_contains
          startBound finishBound
          (GridSegment.contains_of_interiorContains pointInterior)⟩

/-- Scaling two separated integral rectangles leaves room to expand both by
the same coordinate radius when twice that radius is smaller than the scale. -/
theorem
    ClosedGridRectanglesSeparated.scale_both_coordinateRadius
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

/-- Every source segment of the first polyline has a separated endpoint
rectangle from every source segment of the second. -/
def SourceSegmentRectanglesSeparated
    (first second : List Cell) : Prop :=
  ∀ firstSegment ∈ gridPolylineSegments first,
    ∀ secondSegment ∈ gridPolylineSegments second,
      ClosedGridRectanglesSeparated
        firstSegment.coordinateLower firstSegment.coordinateUpper
        secondSegment.coordinateLower secondSegment.coordinateUpper

instance (first second : List Cell) :
    Decidable (SourceSegmentRectanglesSeparated first second) := by
  unfold SourceSegmentRectanglesSeparated
  infer_instance

/-- Strict separation of two orthogonal source routes implies pairwise
separation of all their integral segment rectangles. -/
theorem SourceSegmentRectanglesSeparated.of_strictlyAvoid
    {first second : List Cell}
    (firstOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline first)
    (secondOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline second)
    (avoid :
      RoutesStrictlyAvoidEachOther first second) :
    SourceSegmentRectanglesSeparated first second := by
  have firstAligned :=
    (PeriodicOrthocrossing.orthogonalPolyline_iff_segments
      first).mp firstOrthogonal
  have secondAligned :=
    (PeriodicOrthocrossing.orthogonalPolyline_iff_segments
      second).mp secondOrthogonal
  intro firstSegment firstMember secondSegment secondMember
  have firstEndpoints :=
    gridPolylineSegments_endpoints_mem firstMember
  have secondEndpoints :=
    gridPolylineSegments_endpoints_mem secondMember
  exact
    GridSegment.coordinateRectangles_separated_of_axisAligned
      (firstAligned firstSegment firstMember)
      (secondAligned secondSegment secondMember)
      (avoid.1 firstSegment firstMember
        secondSegment secondMember)
      (avoid.2.1 firstSegment.start firstEndpoints.1
        secondSegment secondMember)
      (avoid.2.1 firstSegment.finish firstEndpoints.2
        secondSegment secondMember)
      (avoid.2.2.1 secondSegment.start secondEndpoints.1
        firstSegment firstMember)
      (avoid.2.2.1 secondSegment.finish secondEndpoints.2
        firstSegment firstMember)
      (avoid.2.2.2 firstSegment.start firstEndpoints.1
        secondSegment.start secondEndpoints.1)
      (avoid.2.2.2 firstSegment.start firstEndpoints.1
        secondSegment.finish secondEndpoints.2)
      (avoid.2.2.2 firstSegment.finish firstEndpoints.2
        secondSegment.start secondEndpoints.1)
      (avoid.2.2.2 firstSegment.finish firstEndpoints.2
        secondSegment.finish secondEndpoints.2)

/-- Pairwise separation of integral source-segment rectangles survives
sufficient scaling, retained-ray rasterization, and unit subdivision as
point-disjointness of the resulting routes. -/
theorem
    unitSubdividedRasterizations_disjoint_of_sourceSegmentRectanglesSeparated
    {factor : Nat}
    (factorPositive : 0 < factor)
    (clearance : 18 < factor)
    (first second : List Cell)
    (firstRetained : RetainedRayPolyline first)
    (secondRetained : RetainedRayPolyline second)
    (firstLength : 2 ≤ first.length)
    (secondLength : 2 ≤ second.length)
    (separated :
      SourceSegmentRectanglesSeparated first second) :
    ∀ point,
      point ∈
          AxisDirection.unitSubdividePolyline
            (rasterizeRetainedPolyline
              (scalePolyline factor first)) →
        point ∈
          AxisDirection.unitSubdividePolyline
            (rasterizeRetainedPolyline
              (scalePolyline factor second)) →
        False := by
  intro point firstMember secondMember
  have firstScaledRetained :=
    firstRetained.scale factorPositive
  have secondScaledRetained :=
    secondRetained.scale factorPositive
  have firstScaledLength :
      2 ≤ (scalePolyline factor first).length := by
    simpa [scalePolyline] using firstLength
  have secondScaledLength :
      2 ≤ (scalePolyline factor second).length := by
    simpa [scalePolyline] using secondLength
  rcases
      unitSubdividedRasterizeRetainedPolyline_point_in_sourceRectangle
        firstScaledRetained firstScaledLength firstMember with
    ⟨firstScaledSegment, firstScaledMember, firstBounded⟩
  rcases
      unitSubdividedRasterizeRetainedPolyline_point_in_sourceRectangle
        secondScaledRetained secondScaledLength secondMember with
    ⟨secondScaledSegment, secondScaledMember, secondBounded⟩
  rw [gridPolylineSegments_scalePolyline] at firstScaledMember
  rw [gridPolylineSegments_scalePolyline] at secondScaledMember
  rcases List.mem_map.mp firstScaledMember with
    ⟨firstSegment, firstSegmentMember, firstSegmentEq⟩
  rcases List.mem_map.mp secondScaledMember with
    ⟨secondSegment, secondSegmentMember, secondSegmentEq⟩
  subst firstScaledSegment
  subst secondScaledSegment
  have factorNonnegativeInt :
      (0 : Int) ≤ factor := by
    exact_mod_cast factorPositive.le
  rw [GridSegment.coordinateLower_scale
      factorNonnegativeInt,
    GridSegment.coordinateUpper_scale
      factorNonnegativeInt] at firstBounded
  rw [GridSegment.coordinateLower_scale
      factorNonnegativeInt,
    GridSegment.coordinateUpper_scale
      factorNonnegativeInt] at secondBounded
  have expandedSeparated :=
    ClosedGridRectanglesSeparated.scale_both_coordinateRadius
      (radius := 9)
      (separated firstSegment firstSegmentMember
        secondSegment secondSegmentMember)
      factorPositive (by omega)
  exact
    (ne_of_inClosedGridRectangles_of_separated
      firstBounded secondBounded expandedSeparated) rfl

/-- Every listed point of the first source has a separated singleton
rectangle from every source segment of the second.  This is the missing
provenance case when the first retained prefix is a singleton. -/
def SourcePointSegmentRectanglesSeparated
    (first second : List Cell) : Prop :=
  ∀ firstPoint ∈ first,
    ∀ secondSegment ∈ gridPolylineSegments second,
      ClosedGridRectanglesSeparated
        firstPoint firstPoint
        secondSegment.coordinateLower secondSegment.coordinateUpper

instance (first second : List Cell) :
    Decidable
      (SourcePointSegmentRectanglesSeparated first second) := by
  unfold SourcePointSegmentRectanglesSeparated
  infer_instance

/-- Point/segment separation handles singleton first routes, while
segment/segment separation handles every nondegenerate first route. -/
def SourcePolylineRectanglesSeparated
    (first second : List Cell) : Prop :=
  SourcePointSegmentRectanglesSeparated first second ∧
    SourceSegmentRectanglesSeparated first second

instance (first second : List Cell) :
    Decidable (SourcePolylineRectanglesSeparated first second) := by
  unfold SourcePolylineRectanglesSeparated
  infer_instance

/-- The rasterization-separation lift also covers a singleton first
polyline.  This is essential for a two-point incidence route, whose
`dropLast` prefix consists only of its clause endpoint. -/
theorem
    unitSubdividedRasterizations_disjoint_of_sourcePolylineRectanglesSeparated
    {factor : Nat}
    (factorPositive : 0 < factor)
    (clearance : 18 < factor)
    (first second : List Cell)
    (firstRetained : RetainedRayPolyline first)
    (secondRetained : RetainedRayPolyline second)
    (firstNonempty : first ≠ [])
    (secondLength : 2 ≤ second.length)
    (separated :
      SourcePolylineRectanglesSeparated first second) :
    ∀ point,
      point ∈
          AxisDirection.unitSubdividePolyline
            (rasterizeRetainedPolyline
              (scalePolyline factor first)) →
        point ∈
          AxisDirection.unitSubdividePolyline
            (rasterizeRetainedPolyline
              (scalePolyline factor second)) →
        False := by
  by_cases firstLength : 2 ≤ first.length
  · exact
      unitSubdividedRasterizations_disjoint_of_sourceSegmentRectanglesSeparated
        factorPositive clearance first second
        firstRetained secondRetained firstLength secondLength
        separated.2
  · have firstLengthPositive : 0 < first.length := by
      exact List.length_pos_iff.mpr firstNonempty
    have firstLengthOne : first.length = 1 := by
      omega
    rcases first with _ | ⟨firstPoint, rest⟩
    · exact (firstNonempty rfl).elim
    · have restEmpty : rest = [] := by
        cases rest with
        | nil => rfl
        | cons secondPoint rest =>
            simp at firstLengthOne
      subst rest
      intro point firstMember secondMember
      have pointEq :
          point = Cell.scale factor firstPoint := by
        simpa [scalePolyline] using firstMember
      have secondScaledRetained :=
        secondRetained.scale factorPositive
      have secondScaledLength :
          2 ≤ (scalePolyline factor second).length := by
        simpa [scalePolyline] using secondLength
      rcases
          unitSubdividedRasterizeRetainedPolyline_point_in_sourceRectangle
            secondScaledRetained secondScaledLength secondMember with
        ⟨secondScaledSegment, secondScaledMember, secondBounded⟩
      rw [gridPolylineSegments_scalePolyline] at secondScaledMember
      rcases List.mem_map.mp secondScaledMember with
        ⟨secondSegment, secondSegmentMember, secondSegmentEq⟩
      subst secondScaledSegment
      have factorNonnegativeInt :
          (0 : Int) ≤ factor := by
        exact_mod_cast factorPositive.le
      rw [GridSegment.coordinateLower_scale
          factorNonnegativeInt,
        GridSegment.coordinateUpper_scale
          factorNonnegativeInt] at secondBounded
      have firstBounded :
          InClosedGridRectangle
            (coordinateRadiusLower 9
              (Cell.scale factor firstPoint))
            (coordinateRadiusUpper 9
              (Cell.scale factor firstPoint))
            point := by
        rw [pointEq]
        exact
          inClosedGridRectangle_coordinateRadius
            (withinCoordinateRadius_refl 9
              (Cell.scale factor firstPoint))
      have expandedSeparated :=
        ClosedGridRectanglesSeparated.scale_both_coordinateRadius
          (radius := 9)
          (separated.1 firstPoint (by simp)
            secondSegment secondSegmentMember)
          factorPositive (by omega)
      exact
        (ne_of_inClosedGridRectangles_of_separated
          firstBounded secondBounded expandedSeparated) rfl

/-- At the common factor `288`, pairwise source-segment rectangle separation
discharges the exact prefix/route raster-disjointness premise used by the
terminal checkpoint adapter. -/
theorem
    retainedTerminalRefinedUnitPrefixRoute_disjoint_of_sourceSegmentRectanglesSeparated
    (sourceRoute referenceRoute : List Cell)
    (sourceRetained : RetainedRayPolyline sourceRoute)
    (referenceRetained : RetainedRayPolyline referenceRoute)
    (sourcePrefixLength : 2 ≤ sourceRoute.dropLast.length)
    (referenceLength : 2 ≤ referenceRoute.length)
    (separated :
      SourceSegmentRectanglesSeparated
        sourceRoute.dropLast referenceRoute) :
    ∀ point,
      point ∈
          retainedTerminalRefinedUnitPrefixPolyline sourceRoute →
        point ∈
          retainedTerminalRefinedUnitPolyline referenceRoute →
        False := by
  simpa [retainedTerminalRefinedUnitPrefixPolyline,
    retainedTerminalRefinedUnitPolyline] using
    unitSubdividedRasterizations_disjoint_of_sourceSegmentRectanglesSeparated
      (factor := retainedTerminalFanTotalRefinement)
      (by native_decide) (by native_decide)
      sourceRoute.dropLast referenceRoute
      sourceRetained.dropLast referenceRetained
      sourcePrefixLength referenceLength separated

/-- The source-polyline certificate is the general factor-`288` bridge,
including the singleton prefix of a two-point source incidence route. -/
theorem
    retainedTerminalRefinedUnitPrefixRoute_disjoint_of_sourcePolylineRectanglesSeparated
    (sourceRoute referenceRoute : List Cell)
    (sourceRetained : RetainedRayPolyline sourceRoute)
    (referenceRetained : RetainedRayPolyline referenceRoute)
    (sourceLength : 2 ≤ sourceRoute.length)
    (referenceLength : 2 ≤ referenceRoute.length)
    (separated :
      SourcePolylineRectanglesSeparated
        sourceRoute.dropLast referenceRoute) :
    ∀ point,
      point ∈
          retainedTerminalRefinedUnitPrefixPolyline sourceRoute →
        point ∈
          retainedTerminalRefinedUnitPolyline referenceRoute →
        False := by
  have prefixNonempty : sourceRoute.dropLast ≠ [] := by
    intro empty
    have emptyLength := congrArg List.length empty
    simp only [List.length_nil] at emptyLength
    have dropLastLength :
        sourceRoute.dropLast.length + 1 = sourceRoute.length := by
      rw [List.length_dropLast]
      omega
    omega
  simpa [retainedTerminalRefinedUnitPrefixPolyline,
    retainedTerminalRefinedUnitPolyline] using
    unitSubdividedRasterizations_disjoint_of_sourcePolylineRectanglesSeparated
      (factor := retainedTerminalFanTotalRefinement)
      (by native_decide) (by native_decide)
      sourceRoute.dropLast referenceRoute
      sourceRetained.dropLast referenceRetained
      prefixNonempty referenceLength separated

/-- Pairwise source-segment rectangle separation is therefore a sufficient
finite geometric certificate for the mixed source-prefix corridor required
by an angular-fan replacement. -/
theorem
    sourcePrefixCorridorSeparated_of_sourceSegmentRectanglesSeparated
    (sourceRoute referenceRoute : List Cell)
    (referenceTerminal : RetainedTerminalData)
    (sourceRetained : RetainedRayPolyline sourceRoute)
    (referenceRetained : RetainedRayPolyline referenceRoute)
    (sourceLength : 2 ≤ sourceRoute.length)
    (sourcePrefixLength : 2 ≤ sourceRoute.dropLast.length)
    (referenceLength : 2 ≤ referenceRoute.length)
    (referenceClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector referenceRoute) =
        some referenceTerminal)
    (separated :
      SourceSegmentRectanglesSeparated
        sourceRoute.dropLast referenceRoute) :
    SourcePrefixCorridorSeparated
      sourceRoute referenceRoute referenceTerminal.1 := by
  apply
    sourcePrefixCorridorSeparated_of_unitPrefixRouteDisjoint
      sourceRoute referenceRoute referenceTerminal
      sourceRetained referenceRetained
      sourceLength referenceLength referenceClassified
  exact
    retainedTerminalRefinedUnitPrefixRoute_disjoint_of_sourceSegmentRectanglesSeparated
      sourceRoute referenceRoute sourceRetained referenceRetained
      sourcePrefixLength referenceLength separated

/-- The general point/segment plus segment/segment certificate discharges
the terminal corridor for source routes of every allowed length. -/
theorem
    sourcePrefixCorridorSeparated_of_sourcePolylineRectanglesSeparated
    (sourceRoute referenceRoute : List Cell)
    (referenceTerminal : RetainedTerminalData)
    (sourceRetained : RetainedRayPolyline sourceRoute)
    (referenceRetained : RetainedRayPolyline referenceRoute)
    (sourceLength : 2 ≤ sourceRoute.length)
    (referenceLength : 2 ≤ referenceRoute.length)
    (referenceClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector referenceRoute) =
        some referenceTerminal)
    (separated :
      SourcePolylineRectanglesSeparated
        sourceRoute.dropLast referenceRoute) :
    SourcePrefixCorridorSeparated
      sourceRoute referenceRoute referenceTerminal.1 := by
  apply
    sourcePrefixCorridorSeparated_of_unitPrefixRouteDisjoint
      sourceRoute referenceRoute referenceTerminal
      sourceRetained referenceRetained
      sourceLength referenceLength referenceClassified
  exact
    retainedTerminalRefinedUnitPrefixRoute_disjoint_of_sourcePolylineRectanglesSeparated
      sourceRoute referenceRoute sourceRetained referenceRetained
      sourceLength referenceLength separated

end PeriodicEightOccurrenceSplit
end LeanTrominoes
