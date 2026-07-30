import LeanTrominoes.OrthogonalPolylineMiddleCoarsening
import LeanTrominoes.OrthogonalPolylineUnitSubdivisionContacts
import LeanTrominoes.RetainedTerminalEnvelopeCheckpoints

/-!
# Retained terminal checkpoints survive rasterization

The finite terminal-envelope certificate produces exact integral points on
the refined straight source segments.  This file connects those geometric
points to the executable orthogonal route representation.

First, every lattice point of an axis-aligned segment is listed by ordered
unit subdivision, and every source segment rasterization embeds in the
rasterization of its whole retained polyline.  Second, every primitive
checkpoint of a retained ray is listed after rasterization and unit
subdivision, including the long axis rays that rasterization itself leaves
as a single segment.
-/

namespace LeanTrominoes

namespace AxisDirection

/-- Ordered unit subdivision lists every lattice point on its source
axis-aligned segment. -/
theorem mem_unitSegmentPoints_of_contains
    {first second point : Cell}
    (contains : (GridSegment.mk first second).Contains point) :
    point ∈ unitSegmentPoints first second := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases point with ⟨pointX, pointY⟩
  simp only [GridSegment.Contains, GridSegment.IsHorizontal,
    GridSegment.IsVertical, GridSegment.Between] at contains
  rcases contains with
      ⟨horizontal, pointYEq, between⟩ |
      ⟨vertical, pointXEq, between⟩
  · rcases horizontal with ⟨firstYEq, xNe⟩
    subst secondY
    subst pointY
    rcases between with forward | backward
    · refine List.mem_map.mpr
        ⟨(pointX - firstX).toNat, ?_, ?_⟩
      · apply List.mem_range.mpr
        simp only [segmentLength, sub_self, Int.natAbs_zero,
          add_zero]
        have indexCast :
            ((pointX - firstX).toNat : Int) =
              pointX - firstX :=
          Int.toNat_of_nonneg (by omega)
        have lengthCast :
            ((secondX - firstX).natAbs : Int) =
              secondX - firstX :=
          Int.natAbs_of_nonneg (by omega)
        omega
      · have direction :
            between (firstX, firstY) (secondX, firstY) =
              .east :=
          (between_eq_east_iff _ _).mpr ⟨rfl, by omega⟩
        rw [show
          ((pointX - firstX).toNat : Int) =
            pointX - firstX by
              exact Int.toNat_of_nonneg (by omega)]
        simp [direction, step, Cell.add, Cell.scale]
    · refine List.mem_map.mpr
        ⟨(firstX - pointX).toNat, ?_, ?_⟩
      · apply List.mem_range.mpr
        simp only [segmentLength, sub_self, Int.natAbs_zero,
          add_zero]
        have indexCast :
            ((firstX - pointX).toNat : Int) =
              firstX - pointX :=
          Int.toNat_of_nonneg (by omega)
        have lengthCast :
            ((secondX - firstX).natAbs : Int) =
              firstX - secondX := by
          rw [show secondX - firstX =
              -(firstX - secondX) by omega,
            Int.natAbs_neg]
          exact Int.natAbs_of_nonneg (by omega)
        omega
      · have direction :
            between (firstX, firstY) (secondX, firstY) =
              .west :=
          (between_eq_west_iff _ _).mpr ⟨rfl, by omega⟩
        rw [show
          ((firstX - pointX).toNat : Int) =
            firstX - pointX by
              exact Int.toNat_of_nonneg (by omega)]
        simp [direction, step, Cell.add, Cell.scale]
  · rcases vertical with ⟨firstXEq, yNe⟩
    subst secondX
    subst pointX
    rcases between with forward | backward
    · refine List.mem_map.mpr
        ⟨(pointY - firstY).toNat, ?_, ?_⟩
      · apply List.mem_range.mpr
        simp only [segmentLength, sub_self, Int.natAbs_zero,
          zero_add]
        have indexCast :
            ((pointY - firstY).toNat : Int) =
              pointY - firstY :=
          Int.toNat_of_nonneg (by omega)
        have lengthCast :
            ((secondY - firstY).natAbs : Int) =
              secondY - firstY :=
          Int.natAbs_of_nonneg (by omega)
        omega
      · have direction :
            between (firstX, firstY) (firstX, secondY) =
              .north :=
          (between_eq_north_iff _ _).mpr ⟨rfl, by omega⟩
        rw [show
          ((pointY - firstY).toNat : Int) =
            pointY - firstY by
              exact Int.toNat_of_nonneg (by omega)]
        simp [direction, step, Cell.add, Cell.scale]
    · refine List.mem_map.mpr
        ⟨(firstY - pointY).toNat, ?_, ?_⟩
      · apply List.mem_range.mpr
        simp only [segmentLength, sub_self, Int.natAbs_zero,
          zero_add]
        have indexCast :
            ((firstY - pointY).toNat : Int) =
              firstY - pointY :=
          Int.toNat_of_nonneg (by omega)
        have lengthCast :
            ((secondY - firstY).natAbs : Int) =
              firstY - secondY := by
          rw [show secondY - firstY =
              -(firstY - secondY) by omega,
            Int.natAbs_neg]
          exact Int.natAbs_of_nonneg (by omega)
        omega
      · have direction :
            between (firstX, firstY) (firstX, secondY) =
              .south :=
          (between_eq_south_iff _ _).mpr ⟨rfl, by omega⟩
        rw [show
          ((firstY - pointY).toNat : Int) =
            firstY - pointY by
              exact Int.toNat_of_nonneg (by omega)]
        simp [direction, step, Cell.add, Cell.scale]

/-- Every listed point of an orthogonal polyline remains listed after
ordered unit subdivision. -/
theorem mem_unitSubdividePolyline_of_mem
    {points : List Cell}
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points)
    {point : Cell}
    (member : point ∈ points) :
    point ∈ unitSubdividePolyline points := by
  induction points using List.twoStepInduction generalizing point with
  | nil =>
      simp at member
  | singleton only =>
      simpa using member
  | cons_cons first second rest _ tailInduction =>
      have parts :=
        (List.isChain_cons_cons.mp orthogonal :
          (GridSegment.mk first second).IsAxisAligned ∧
            PeriodicOrthocrossing.OrthogonalPolyline
              (second :: rest))
      rw [unitSubdividePolyline]
      apply
        (mem_joinAtEndpoint_iff
          (unitSegmentPoints_getLast? parts.1)
          (by
            simpa using
              unitSubdividePolyline_head?
                (points := second :: rest) (by simp))).mpr
      simp only [List.mem_cons] at member
      rcases member with rfl | tailMember
      · left
        exact List.mem_of_mem_head?
          (by simp [unitSegmentPoints_head?])
      · right
        exact tailInduction second parts.2 (by
          simpa using tailMember)

/-- Every lattice point on any segment of an orthogonal polyline is listed
after ordered unit subdivision. -/
theorem mem_unitSubdividePolyline_of_segment_contains
    {points : List Cell}
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points)
    {segment : GridSegment}
    (segmentMember :
      segment ∈ gridPolylineSegments points)
    {point : Cell}
    (contains : segment.Contains point) :
    point ∈ unitSubdividePolyline points := by
  induction points using List.twoStepInduction
      generalizing segment point with
  | nil =>
      simp [gridPolylineSegments] at segmentMember
  | singleton only =>
      simp [gridPolylineSegments] at segmentMember
  | cons_cons first second rest _ tailInduction =>
      have parts :=
        (List.isChain_cons_cons.mp orthogonal :
          (GridSegment.mk first second).IsAxisAligned ∧
            PeriodicOrthocrossing.OrthogonalPolyline
              (second :: rest))
      simp only [gridPolylineSegments, List.mem_cons]
        at segmentMember
      rw [unitSubdividePolyline]
      apply
        (mem_joinAtEndpoint_iff
          (unitSegmentPoints_getLast? parts.1)
          (by
            simpa using
              unitSubdividePolyline_head?
                (points := second :: rest) (by simp))).mpr
      rcases segmentMember with rfl | tailMember
      · left
        exact mem_unitSegmentPoints_of_contains contains
      · right
        exact
          tailInduction second parts.2 tailMember contains

end AxisDirection

namespace PeriodicEightOccurrenceSplit

/-- A positive multiple of a compass primitive receives the exact
corresponding retained-ray classification. -/
@[simp]
theorem retainedRayClassify_scale_compassUnitVector
    (port : OccurrenceSplitRing.Port)
    (length : Nat)
    (positive : 0 < length) :
    retainedRayClassify
        (Cell.scale length port.unitVector) =
      some (.compass port length) := by
  unfold retainedRayClassify
  rw [terminalPort_scale_unitVector port
    (by exact_mod_cast positive)]
  cases port <;>
    simp [compassLength,
      OccurrenceSplitRing.Port.unitVector,
      Cell.scale]

/-- A positive cardinal compass ray is represented by its direct endpoint
pair. -/
theorem compassRay_eq_pair_of_cardinal
    (port : OccurrenceSplitRing.Port)
    (length : Nat)
    (positive : 0 < length)
    (start : Cell)
    (cardinal :
      port = .north ∨ port = .east ∨
        port = .south ∨ port = .west) :
    compassRay port length start =
      [start,
        Cell.add start
          (Cell.scale length port.unitVector)] := by
  rcases cardinal with rfl | rfl | rfl | rfl <;>
    cases length with
    | zero => simp at positive
    | succ length => rfl

/-- Rasterization leaves a genuine axis-aligned segment as that same direct
two-point segment. -/
theorem rasterizeRetainedSegment_eq_of_axisAligned
    (segment : GridSegment)
    (aligned : segment.IsAxisAligned) :
    rasterizeRetainedSegment segment =
      [segment.start, segment.finish] := by
  rcases segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  simp only [GridSegment.IsAxisAligned,
    GridSegment.IsHorizontal, GridSegment.IsVertical]
    at aligned
  rcases aligned with
      ⟨sameY, differentX⟩ |
      ⟨sameX, differentY⟩
  · subst finishY
    by_cases forward : startX < finishX
    · let length := (finishX - startX).toNat
      have lengthPositive : 0 < length := by
        dsimp [length]
        omega
      have lengthCast :
          (length : Int) = finishX - startX := by
        exact Int.toNat_of_nonneg (by omega)
      have vectorEq :
          (finishX - startX, 0) =
            Cell.scale length
              OccurrenceSplitRing.Port.east.unitVector := by
        simp [OccurrenceSplitRing.Port.unitVector,
          Cell.scale, lengthCast]
      have classification :
          retainedRayClassify (finishX - startX, 0) =
            some (.compass OccurrenceSplitRing.Port.east length) := by
        rw [vectorEq]
        exact retainedRayClassify_scale_compassUnitVector
          .east length lengthPositive
      unfold rasterizeRetainedSegment
      simp only [Cell.sub, sub_self, classification]
      change compassRay .east length (startX, startY) = _
      rw [compassRay_eq_pair_of_cardinal
        .east length lengthPositive _ (by simp)]
      simp [OccurrenceSplitRing.Port.unitVector,
        Cell.add, Cell.scale, lengthCast]
    · have backward : finishX < startX := by omega
      let length := (startX - finishX).toNat
      have lengthPositive : 0 < length := by
        dsimp [length]
        omega
      have lengthCast :
          (length : Int) = startX - finishX := by
        exact Int.toNat_of_nonneg (by omega)
      have vectorEq :
          (finishX - startX, 0) =
            Cell.scale length
              OccurrenceSplitRing.Port.west.unitVector := by
        simp [OccurrenceSplitRing.Port.unitVector,
          Cell.scale, lengthCast]
      have classification :
          retainedRayClassify (finishX - startX, 0) =
            some (.compass OccurrenceSplitRing.Port.west length) := by
        rw [vectorEq]
        exact retainedRayClassify_scale_compassUnitVector
          .west length lengthPositive
      unfold rasterizeRetainedSegment
      simp only [Cell.sub, sub_self, classification]
      change compassRay .west length (startX, startY) = _
      rw [compassRay_eq_pair_of_cardinal
        .west length lengthPositive _ (by simp)]
      simp [OccurrenceSplitRing.Port.unitVector,
        Cell.add, Cell.scale, lengthCast]
  · subst finishX
    by_cases forward : startY < finishY
    · let length := (finishY - startY).toNat
      have lengthPositive : 0 < length := by
        dsimp [length]
        omega
      have lengthCast :
          (length : Int) = finishY - startY := by
        exact Int.toNat_of_nonneg (by omega)
      have vectorEq :
          (0, finishY - startY) =
            Cell.scale length
              OccurrenceSplitRing.Port.south.unitVector := by
        simp [OccurrenceSplitRing.Port.unitVector,
          Cell.scale, lengthCast]
      have classification :
          retainedRayClassify (0, finishY - startY) =
            some (.compass OccurrenceSplitRing.Port.south length) := by
        rw [vectorEq]
        exact retainedRayClassify_scale_compassUnitVector
          .south length lengthPositive
      unfold rasterizeRetainedSegment
      simp only [Cell.sub, sub_self, classification]
      change compassRay .south length (startX, startY) = _
      rw [compassRay_eq_pair_of_cardinal
        .south length lengthPositive _ (by simp)]
      simp [OccurrenceSplitRing.Port.unitVector,
        Cell.add, Cell.scale, lengthCast]
    · have backward : finishY < startY := by omega
      let length := (startY - finishY).toNat
      have lengthPositive : 0 < length := by
        dsimp [length]
        omega
      have lengthCast :
          (length : Int) = startY - finishY := by
        exact Int.toNat_of_nonneg (by omega)
      have vectorEq :
          (0, finishY - startY) =
            Cell.scale length
              OccurrenceSplitRing.Port.north.unitVector := by
        simp [OccurrenceSplitRing.Port.unitVector,
          Cell.scale, lengthCast]
      have classification :
          retainedRayClassify (0, finishY - startY) =
            some (.compass OccurrenceSplitRing.Port.north length) := by
        rw [vectorEq]
        exact retainedRayClassify_scale_compassUnitVector
          .north length lengthPositive
      unfold rasterizeRetainedSegment
      simp only [Cell.sub, sub_self, classification]
      change compassRay .north length (startX, startY) = _
      rw [compassRay_eq_pair_of_cardinal
        .north length lengthPositive _ (by simp)]
      simp [OccurrenceSplitRing.Port.unitVector,
        Cell.add, Cell.scale, lengthCast]

/-- Every segment introduced while rasterizing one source segment remains a
segment of the rasterized whole source polyline. -/
theorem rasterizeRetainedSegment_segment_mem_rasterizeRetainedPolyline
    {points : List Cell}
    {sourceSegment rasterSegment : GridSegment}
    (sourceMember :
      sourceSegment ∈ gridPolylineSegments points)
    (rasterMember :
      rasterSegment ∈
        gridPolylineSegments
          (rasterizeRetainedSegment sourceSegment)) :
    rasterSegment ∈
      gridPolylineSegments
        (rasterizeRetainedPolyline points) := by
  induction points using List.twoStepInduction
      generalizing sourceSegment with
  | nil =>
      simp [gridPolylineSegments] at sourceMember
  | singleton only =>
      simp [gridPolylineSegments] at sourceMember
  | cons_cons first second rest _ tailInduction =>
      simp only [gridPolylineSegments, List.mem_cons]
        at sourceMember
      rw [rasterizeRetainedPolyline_cons_cons,
        PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.gridPolylineSegments_joinAtEndpoint
          (rasterizeRetainedSegment_getLast?
            (GridSegment.mk first second))
          (by
            rw [rasterizeRetainedPolyline_head?]
            rfl),
        List.mem_append]
      rcases sourceMember with rfl | tailMember
      · exact Or.inl rasterMember
      · exact Or.inr
          (tailInduction second tailMember rasterMember)

/-- Every listed point introduced while rasterizing one source segment
remains listed in the rasterization of the whole source polyline. -/
theorem rasterizeRetainedSegment_point_mem_rasterizeRetainedPolyline
    {points : List Cell}
    {sourceSegment : GridSegment}
    (sourceMember :
      sourceSegment ∈ gridPolylineSegments points)
    {point : Cell}
    (pointMember :
      point ∈ rasterizeRetainedSegment sourceSegment) :
    point ∈ rasterizeRetainedPolyline points := by
  induction points using List.twoStepInduction
      generalizing sourceSegment point with
  | nil =>
      simp [gridPolylineSegments] at sourceMember
  | singleton only =>
      simp [gridPolylineSegments] at sourceMember
  | cons_cons first second rest _ tailInduction =>
      simp only [gridPolylineSegments, List.mem_cons]
        at sourceMember
      rw [rasterizeRetainedPolyline_cons_cons]
      apply
        (mem_joinAtEndpoint_iff
          (rasterizeRetainedSegment_getLast?
            (GridSegment.mk first second))
          (by
            rw [rasterizeRetainedPolyline_head?]
            rfl)).mpr
      rcases sourceMember with rfl | tailMember
      · exact Or.inl pointMember
      · exact Or.inr
          (tailInduction second tailMember pointMember)

/-- Unit-subdivided points of one retained source segment's rasterization
remain listed after rasterizing and unit-subdividing the whole polyline. -/
theorem
    unitSubdividedRasterizeRetainedSegment_point_mem_whole
    {points : List Cell}
    (retained : RetainedRayPolyline points)
    {sourceSegment : GridSegment}
    (sourceMember :
      sourceSegment ∈ gridPolylineSegments points)
    {point : Cell}
    (pointMember :
      point ∈
        AxisDirection.unitSubdividePolyline
          (rasterizeRetainedSegment sourceSegment)) :
    point ∈
      AxisDirection.unitSubdividePolyline
        (rasterizeRetainedPolyline points) := by
  have sourceRetained :=
    retained sourceSegment sourceMember
  have sourceOrthogonal :=
    rasterizeRetainedSegment_orthogonal
      sourceSegment sourceRetained
  have wholeOrthogonal :=
    rasterizeRetainedPolyline_orthogonal retained
  rcases
      AxisDirection.unitSubdividePolyline_mem_original_or_segmentInterior
        sourceOrthogonal pointMember with
    rawPoint | ⟨rasterSegment, rasterMember, interior⟩
  · exact
      AxisDirection.mem_unitSubdividePolyline_of_mem
        wholeOrthogonal
        (rasterizeRetainedSegment_point_mem_rasterizeRetainedPolyline
          sourceMember rawPoint)
  · exact
      AxisDirection.mem_unitSubdividePolyline_of_segment_contains
        wholeOrthogonal
        (rasterizeRetainedSegment_segment_mem_rasterizeRetainedPolyline
          sourceMember rasterMember)
        (GridSegment.contains_of_interiorContains interior)

/-- A lattice point on an axis-aligned source segment is listed after
rasterizing and unit-subdividing the whole retained source polyline. -/
theorem
    axisSegmentPoint_mem_unitSubdividedRasterizeRetainedPolyline
    {points : List Cell}
    (retained : RetainedRayPolyline points)
    {segment : GridSegment}
    (segmentMember :
      segment ∈ gridPolylineSegments points)
    {point : Cell}
    (contains : segment.Contains point) :
    point ∈
      AxisDirection.unitSubdividePolyline
        (rasterizeRetainedPolyline points) := by
  have aligned : segment.IsAxisAligned := by
    exact contains.elim (fun horizontal => Or.inl horizontal.1)
      (fun vertical => Or.inr vertical.1)
  have rasterSegmentMember :
      segment ∈
        gridPolylineSegments
          (rasterizeRetainedPolyline points) := by
    apply
      rasterizeRetainedSegment_segment_mem_rasterizeRetainedPolyline
        segmentMember
    rw [rasterizeRetainedSegment_eq_of_axisAligned segment aligned]
    simp [gridPolylineSegments]
  exact
    AxisDirection.mem_unitSubdividePolyline_of_segment_contains
      (rasterizeRetainedPolyline_orthogonal retained)
      rasterSegmentMember contains

/-- Every listed source point of a nondegenerate retained polyline remains
listed after rasterizing and unit-subdividing the whole polyline. -/
theorem sourcePoint_mem_unitSubdividedRasterizeRetainedPolyline
    {points : List Cell}
    (retained : RetainedRayPolyline points)
    (length : 2 ≤ points.length)
    {point : Cell}
    (pointMember : point ∈ points) :
    point ∈
      AxisDirection.unitSubdividePolyline
        (rasterizeRetainedPolyline points) := by
  rcases
      exists_gridPolylineSegment_of_mem
        length pointMember with
    ⟨sourceSegment, sourceMember, pointAtStart | pointAtFinish⟩
  · subst point
    apply
      unitSubdividedRasterizeRetainedSegment_point_mem_whole
        retained sourceMember
    apply
      AxisDirection.mem_unitSubdividePolyline_of_mem
        (rasterizeRetainedSegment_orthogonal
          sourceSegment (retained sourceSegment sourceMember))
    exact List.mem_of_mem_head?
      (rasterizeRetainedSegment_head? sourceSegment)
  · subst point
    apply
      unitSubdividedRasterizeRetainedSegment_point_mem_whole
        retained sourceMember
    apply
      AxisDirection.mem_unitSubdividePolyline_of_mem
        (rasterizeRetainedSegment_orthogonal
          sourceSegment (retained sourceSegment sourceMember))
    exact
      mem_of_getLast?_eq_some
        (rasterizeRetainedSegment_getLast? sourceSegment)

/-- A route with at least two points contains its exact final segment from
`polylineLastEntrance` to its advertised last point. -/
theorem finalGridSegment_mem
    (route : List Cell)
    (routeLength : 2 ≤ route.length) :
    GridSegment.mk
        (polylineLastEntrance route)
        (route.getLastD (0, 0)) ∈
      gridPolylineSegments route := by
  generalize reversedEq : route.reverse = reversed
  cases reversed with
  | nil =>
      have routeEq : route = [] := by
        simpa using congrArg List.reverse reversedEq
      subst route
      simp at routeLength
  | cons target rest =>
      cases rest with
      | nil =>
          have routeEq : route = [target] := by
            simpa using congrArg List.reverse reversedEq
          subst route
          simp at routeLength
      | cons entrance rest =>
          have routeEq :
              route =
                (target :: entrance :: rest).reverse := by
            simpa using congrArg List.reverse reversedEq
          subst route
          rw [show
            (target :: entrance :: rest).reverse =
              (rest.reverse ++ [entrance]) ++ [target] by
                simp]
          rw [gridPolylineSegments_append_singleton_of_ne_nil
            (rest.reverse ++ [entrance])
            entrance target (by simp)]
          simp [polylineLastEntrance, polylineFirstExit]

/-- A primitive return point of a diagonal staircase is explicitly listed
by that staircase. -/
theorem diagonalStaircase_checkpoint_mem
    (horizontal vertical : Int)
    (length index : Nat)
    (indexBound : index ≤ length)
    (start : Cell) :
    Cell.add start
        (Cell.scale index (horizontal, vertical)) ∈
      diagonalStaircase horizontal vertical length start := by
  induction length generalizing index start with
  | zero =>
      have : index = 0 := by omega
      subst index
      simp [diagonalStaircase, Cell.add, Cell.scale]
  | succ length induction =>
      by_cases indexZero : index = 0
      · subst index
        simp [diagonalStaircase, Cell.add, Cell.scale]
      · have indexPositive : 0 < index := Nat.pos_of_ne_zero indexZero
        let previous := index - 1
        have previousBound : previous ≤ length := by
          dsimp [previous]
          omega
        have tailMember :=
          induction previous previousBound
            (Cell.add start (horizontal, vertical))
        have checkpointEq :
            Cell.add
                (Cell.add start (horizontal, vertical))
                (Cell.scale previous (horizontal, vertical)) =
              Cell.add start
                (Cell.scale index (horizontal, vertical)) := by
          have previousSucc : previous + 1 = index := by
            dsimp [previous]
            omega
          rw [← previousSucc]
          rcases start with ⟨startX, startY⟩
          simp [Cell.add, Cell.scale]
          constructor <;> ring
        simp only [diagonalStaircase, List.mem_cons]
        exact Or.inr (Or.inr (checkpointEq ▸ tailMember))

/-- A primitive block-return point is explicitly listed by the repeated
routed-clause staircase. -/
theorem routedClauseRay_checkpoint_mem
    (arm : PlanarThreeSAT.DuplicatorArm)
    (length index : Nat)
    (indexBound : index ≤ length)
    (start : Cell) :
    Cell.add start
        (Cell.scale index
          (routedClauseRayPrimitive arm)) ∈
      routedClauseRay arm length start := by
  induction length generalizing index start with
  | zero =>
      have : index = 0 := by omega
      subst index
      simp [routedClauseRay, Cell.add, Cell.scale]
  | succ length induction =>
      rw [routedClauseRay]
      apply
        (mem_joinAtEndpoint_iff
          (routedClauseRayBlock_getLast? arm start)
          (routedClauseRay_head? arm length
            (Cell.add start
              (routedClauseRayPrimitive arm)))).mpr
      by_cases indexZero : index = 0
      · subst index
        left
        simpa [Cell.add, Cell.scale] using
          List.mem_of_mem_head?
            (routedClauseRayBlock_head? arm start)
      · right
        have indexPositive : 0 < index := Nat.pos_of_ne_zero indexZero
        let previous := index - 1
        have previousBound : previous ≤ length := by
          dsimp [previous]
          omega
        have tailMember :=
          induction previous previousBound
            (Cell.add start
              (routedClauseRayPrimitive arm))
        have checkpointEq :
            Cell.add
                (Cell.add start
                  (routedClauseRayPrimitive arm))
                (Cell.scale previous
                  (routedClauseRayPrimitive arm)) =
              Cell.add start
                (Cell.scale index
                  (routedClauseRayPrimitive arm)) := by
          have previousSucc : previous + 1 = index := by
            dsimp [previous]
            omega
          rw [← previousSucc]
          rcases start with ⟨startX, startY⟩
          rcases routedClauseRayPrimitive arm with
            ⟨primitiveX, primitiveY⟩
          simp [Cell.add, Cell.scale]
          constructor <;> ring
        exact checkpointEq ▸ tailMember

/-- Every primitive checkpoint of a retained ray is listed after
rasterization and ordered unit subdivision. -/
theorem RetainedRay.checkpoint_mem_unitSubdividedRasterization
    (ray : RetainedRay)
    (start : Cell)
    (index : Nat)
    (indexBound : index ≤ ray.length) :
    Cell.add start
        (Cell.scale index ray.primitive) ∈
      AxisDirection.unitSubdividePolyline
        (ray.rasterize start) := by
  have orthogonal := ray.rasterize_orthogonal start
  cases ray with
  | compass port length =>
      cases length with
      | zero =>
          have : index = 0 := by
            simpa [RetainedRay.length] using indexBound
          subst index
          simp [RetainedRay.rasterize, RetainedRay.primitive,
            compassRay, Cell.add, Cell.scale]
      | succ length =>
          cases port with
          | northwest | northeast | southeast | southwest =>
              apply
                AxisDirection.mem_unitSubdividePolyline_of_mem
                  orthogonal
              simpa [RetainedRay.rasterize,
                RetainedRay.primitive, compassRay,
                OccurrenceSplitRing.Port.unitVector] using
                diagonalStaircase_checkpoint_mem _ _
                  (length + 1) index
                  (by simpa [RetainedRay.length] using indexBound)
                  start
          | north =>
              apply
                AxisDirection.mem_unitSubdividePolyline_of_segment_contains
                  orthogonal
                  (segment := GridSegment.mk start
                    (Cell.add start
                      (Cell.scale (length + 1)
                        OccurrenceSplitRing.Port.north.unitVector)))
                  (by
                    simp [RetainedRay.rasterize,
                      compassRay, gridPolylineSegments,
                      OccurrenceSplitRing.Port.unitVector])
              rcases start with ⟨startX, startY⟩
              simp [GridSegment.Contains,
                GridSegment.IsHorizontal,
                GridSegment.IsVertical, GridSegment.Between,
                RetainedRay.length, RetainedRay.primitive,
                OccurrenceSplitRing.Port.unitVector,
                Cell.add, Cell.scale] at indexBound ⊢ <;>
                omega
          | east =>
              apply
                AxisDirection.mem_unitSubdividePolyline_of_segment_contains
                  orthogonal
                  (segment := GridSegment.mk start
                    (Cell.add start
                      (Cell.scale (length + 1)
                        OccurrenceSplitRing.Port.east.unitVector)))
                  (by
                    simp [RetainedRay.rasterize,
                      compassRay, gridPolylineSegments,
                      OccurrenceSplitRing.Port.unitVector])
              rcases start with ⟨startX, startY⟩
              simp [GridSegment.Contains,
                GridSegment.IsHorizontal,
                GridSegment.IsVertical, GridSegment.Between,
                RetainedRay.length, RetainedRay.primitive,
                OccurrenceSplitRing.Port.unitVector,
                Cell.add, Cell.scale] at indexBound ⊢ <;>
                omega
          | south =>
              apply
                AxisDirection.mem_unitSubdividePolyline_of_segment_contains
                  orthogonal
                  (segment := GridSegment.mk start
                    (Cell.add start
                      (Cell.scale (length + 1)
                        OccurrenceSplitRing.Port.south.unitVector)))
                  (by
                    simp [RetainedRay.rasterize,
                      compassRay, gridPolylineSegments,
                      OccurrenceSplitRing.Port.unitVector])
              rcases start with ⟨startX, startY⟩
              simp [GridSegment.Contains,
                GridSegment.IsHorizontal,
                GridSegment.IsVertical, GridSegment.Between,
                RetainedRay.length, RetainedRay.primitive,
                OccurrenceSplitRing.Port.unitVector,
                Cell.add, Cell.scale] at indexBound ⊢ <;>
                omega
          | west =>
              apply
                AxisDirection.mem_unitSubdividePolyline_of_segment_contains
                  orthogonal
                  (segment := GridSegment.mk start
                    (Cell.add start
                      (Cell.scale (length + 1)
                        OccurrenceSplitRing.Port.west.unitVector)))
                  (by
                    simp [RetainedRay.rasterize,
                      compassRay, gridPolylineSegments,
                      OccurrenceSplitRing.Port.unitVector])
              rcases start with ⟨startX, startY⟩
              simp [GridSegment.Contains,
                GridSegment.IsHorizontal,
                GridSegment.IsVertical, GridSegment.Between,
                RetainedRay.length, RetainedRay.primitive,
                OccurrenceSplitRing.Port.unitVector,
                Cell.add, Cell.scale] at indexBound ⊢ <;>
                omega
  | routedClause arm length =>
      apply
        AxisDirection.mem_unitSubdividePolyline_of_mem
          orthogonal
      simpa [RetainedRay.rasterize,
        RetainedRay.length, RetainedRay.primitive] using
        routedClauseRay_checkpoint_mem arm length index
          (by simpa [RetainedRay.length] using indexBound)
          start

/-- Forward retained ray of the fully refined discarded terminal segment. -/
def retainedTerminalRefinedForwardRay
    (terminal : RetainedTerminalData) : RetainedRay :=
  match terminal.1 with
  | .compass port =>
      .compass (oppositePort port)
        (retainedTerminalFanTotalRefinement * terminal.2)
  | .routedClause arm =>
      .routedClause arm
        (retainedTerminalFanTotalRefinement * terminal.2)

@[simp]
theorem retainedTerminalRefinedForwardRay_length
    (terminal : RetainedTerminalData) :
    (retainedTerminalRefinedForwardRay terminal).length =
      retainedTerminalFanTotalRefinement * terminal.2 := by
  rcases terminal with ⟨direction, length⟩
  cases direction <;> rfl

/-- The forward refined ray primitive is the negation of the backwards
terminal primitive. -/
theorem retainedTerminalRefinedForwardRay_primitive
    (terminal : RetainedTerminalData) :
    (retainedTerminalRefinedForwardRay terminal).primitive =
      Cell.sub (0, 0) terminal.1.primitive := by
  rcases terminal with ⟨direction, length⟩
  cases direction with
  | compass port =>
      cases port <;>
        simp [retainedTerminalRefinedForwardRay,
          RetainedRay.primitive,
          RetainedTerminalDirection.primitive,
          oppositePort, OccurrenceSplitRing.Port.unitVector,
          Cell.sub]
  | routedClause arm =>
      cases arm <;>
        simp [retainedTerminalRefinedForwardRay,
          RetainedRay.primitive,
          RetainedTerminalDirection.primitive,
          routedClauseRayPrimitive, Cell.sub]

/-- The executable retained-ray classifier recognizes the exact forward
ray of every positive refined terminal. -/
theorem retainedRayClassify_refinedTerminalForwardVector
    (terminal : RetainedTerminalData)
    (lengthPositive : 0 < terminal.2) :
    retainedRayClassify
        (Cell.scale
          (retainedTerminalFanTotalRefinement * terminal.2)
          (Cell.sub (0, 0) terminal.1.primitive)) =
      some (retainedTerminalRefinedForwardRay terminal) := by
  have productPositive :
      0 <
        retainedTerminalFanTotalRefinement * terminal.2 :=
    Nat.mul_pos (by native_decide) lengthPositive
  rcases terminal with ⟨direction, length⟩
  simp only at lengthPositive productPositive
  cases direction with
  | compass port =>
      have vectorEq :
          Cell.scale
              (retainedTerminalFanTotalRefinement * length)
              (Cell.sub (0, 0)
                (RetainedTerminalDirection.compass port).primitive) =
            Cell.scale
              (retainedTerminalFanTotalRefinement * length)
              (oppositePort port).unitVector := by
        cases port <;>
          simp [RetainedTerminalDirection.primitive,
            oppositePort, OccurrenceSplitRing.Port.unitVector,
            Cell.sub, Cell.scale]
      rw [vectorEq]
      simpa [retainedTerminalRefinedForwardRay] using
        retainedRayClassify_scale_compassUnitVector
          (oppositePort port)
          (retainedTerminalFanTotalRefinement * length)
          productPositive
  | routedClause arm =>
      have vectorEq :
          Cell.scale
              (retainedTerminalFanTotalRefinement * length)
              (Cell.sub (0, 0)
                (RetainedTerminalDirection.routedClause arm).primitive) =
            Cell.scale
              (retainedTerminalFanTotalRefinement * length)
              (routedClauseRayPrimitive arm) := by
        cases arm <;>
          simp [RetainedTerminalDirection.primitive,
            routedClauseRayPrimitive, Cell.sub, Cell.scale]
      rw [vectorEq]
      have terminalNone :
          terminalPort
              (Cell.scale
                (retainedTerminalFanTotalRefinement * length)
                (routedClauseRayPrimitive arm)) =
            none := by
        have factorPositiveInt :
            (0 : Int) <
              retainedTerminalFanTotalRefinement * length := by
          exact_mod_cast productPositive
        rw [terminalPort_scale factorPositiveInt]
        cases arm <;> rfl
      have routedClassified :
          routedClauseRayClassify
              (Cell.scale
                (retainedTerminalFanTotalRefinement * length)
                (routedClauseRayPrimitive arm)) =
            some
              (arm,
                retainedTerminalFanTotalRefinement * length) := by
        simpa only [Nat.cast_mul] using
          routedClauseRayClassify_scale arm productPositive
      unfold retainedRayClassify
      rw [terminalNone, routedClassified]
      simp [retainedTerminalRefinedForwardRay]

/-- Rasterizing a classified route's scaled discarded final segment is
exactly rasterizing its canonical refined forward terminal ray. -/
theorem rasterizeRetainedScaledFinalSegment_eq
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal) :
    rasterizeRetainedSegment
        (GridSegment.mk
          (Cell.scale retainedTerminalFanTotalRefinement
            (polylineLastEntrance route))
          (Cell.scale retainedTerminalFanTotalRefinement
            (route.getLastD (0, 0)))) =
      (retainedTerminalRefinedForwardRay terminal).rasterize
        (Cell.scale retainedTerminalFanTotalRefinement
          (polylineLastEntrance route)) := by
  have entranceEq :=
    polylineLastEntrance_eq_retainedTerminalSplicePoint
      routeLength classified
  have lengthPositive :=
    (retainedTerminalDirectionClassify_sound classified).1
  have vectorEq :
      Cell.sub
          (Cell.scale retainedTerminalFanTotalRefinement
            (route.getLastD (0, 0)))
          (Cell.scale retainedTerminalFanTotalRefinement
            (polylineLastEntrance route)) =
        Cell.scale
          (retainedTerminalFanTotalRefinement * terminal.2)
          (Cell.sub (0, 0) terminal.1.primitive) := by
    rw [entranceEq]
    rcases route.getLastD (0, 0) with ⟨centerX, centerY⟩
    rcases terminal with ⟨direction, length⟩
    rcases direction with _ | _ <;>
      rename_i kind <;>
      cases kind <;>
      apply Prod.ext <;>
      simp [retainedTerminalSplicePoint,
        retainedTerminalFanTotalRefinement_eq,
        RetainedTerminalDirection.primitive,
        OccurrenceSplitRing.Port.unitVector,
        routedClauseRayPrimitive,
        Cell.add, Cell.sub, Cell.scale] <;>
      ring
  unfold rasterizeRetainedSegment
  rw [vectorEq,
    retainedRayClassify_refinedTerminalForwardVector
      terminal lengthPositive]

/-- Every refined checkpoint of a classified terminal is listed by the
unit-subdivided rasterization of its scaled discarded final segment. -/
theorem
    retainedTerminalRefinedCheckpoint_mem_unitSubdividedFinalRasterization
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (point : Cell)
    (checkpoint :
      IsRetainedTerminalRefinedCheckpoint
        route terminal point) :
    point ∈
      AxisDirection.unitSubdividePolyline
        (rasterizeRetainedSegment
          (GridSegment.mk
            (Cell.scale retainedTerminalFanTotalRefinement
              (polylineLastEntrance route))
            (Cell.scale retainedTerminalFanTotalRefinement
              (route.getLastD (0, 0))))) := by
  rcases checkpoint with
    ⟨index, indexBound, pointEq⟩
  let total :=
    retainedTerminalFanTotalRefinement * terminal.2
  let reverseIndex := total - index
  have reverseIndexBound : reverseIndex ≤ total := by
    dsimp [reverseIndex]
    omega
  have reverseAdd : reverseIndex + index = total := by
    dsimp [reverseIndex]
    exact Nat.sub_add_cancel indexBound
  rw [rasterizeRetainedScaledFinalSegment_eq
    route terminal routeLength classified]
  have member :=
    (retainedTerminalRefinedForwardRay terminal
      ).checkpoint_mem_unitSubdividedRasterization
        (Cell.scale retainedTerminalFanTotalRefinement
          (polylineLastEntrance route))
        reverseIndex
        (by
          simpa [total] using reverseIndexBound)
  rw [pointEq]
  convert member using 1
  have entranceEq :=
    polylineLastEntrance_eq_retainedTerminalSplicePoint
      routeLength classified
  rw [entranceEq]
  rcases route.getLastD (0, 0) with ⟨centerX, centerY⟩
  rcases terminal with ⟨direction, length⟩
  generalize primitiveEq :
      direction.primitive = primitive
  rcases primitive with ⟨primitiveX, primitiveY⟩
  have castReverseAdd :
      (reverseIndex : Int) + index = total := by
    exact_mod_cast reverseAdd
  have refinedLengthEq :
      (retainedTerminalFanTotalRefinement : Int) * length =
        (reverseIndex : Int) + index := by
    rw [castReverseAdd]
    simp [total]
  rw [retainedTerminalFanTotalRefinement_eq] at refinedLengthEq
  apply Prod.ext <;>
    simp [retainedTerminalSplicePoint,
      retainedTerminalRefinedForwardRay_primitive,
      primitiveEq, retainedTerminalFanTotalRefinement_eq,
      Cell.add, Cell.sub, Cell.scale]
  · linear_combination -primitiveX * refinedLengthEq
  · linear_combination -primitiveY * refinedLengthEq

/-- Canonical unit-grid realization of a source route at the common
terminal-fan refinement. -/
def retainedTerminalRefinedUnitPolyline
    (route : List Cell) : List Cell :=
  AxisDirection.unitSubdividePolyline
    (rasterizeRetainedPolyline
      (scalePolyline retainedTerminalFanTotalRefinement route))

/-- Every source vertex survives in the canonical refined unit-grid
realization. -/
theorem scaledSourcePoint_mem_retainedTerminalRefinedUnitPolyline
    (route : List Cell)
    (retained : RetainedRayPolyline route)
    (routeLength : 2 ≤ route.length)
    (point : Cell)
    (pointMember : point ∈ route) :
    Cell.scale retainedTerminalFanTotalRefinement point ∈
      retainedTerminalRefinedUnitPolyline route := by
  unfold retainedTerminalRefinedUnitPolyline
  apply
    sourcePoint_mem_unitSubdividedRasterizeRetainedPolyline
      (retained.scale (by native_decide))
      (by simpa [scalePolyline] using routeLength)
  simpa [scalePolyline] using
    List.mem_map_of_mem pointMember

/-- Every refined checkpoint of a classified route's discarded terminal is
also a point of the canonical refined unit-grid realization of the whole
route. -/
theorem
    retainedTerminalRefinedCheckpoint_mem_retainedTerminalRefinedUnitPolyline
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (retained : RetainedRayPolyline route)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (point : Cell)
    (checkpoint :
      IsRetainedTerminalRefinedCheckpoint
        route terminal point) :
    point ∈ retainedTerminalRefinedUnitPolyline route := by
  let finalSegment :=
    GridSegment.mk
      (polylineLastEntrance route)
      (route.getLastD (0, 0))
  have finalMember :
      finalSegment ∈ gridPolylineSegments route := by
    exact finalGridSegment_mem route routeLength
  have scaledFinalMember :
      finalSegment.scale retainedTerminalFanTotalRefinement ∈
        gridPolylineSegments
          (scalePolyline retainedTerminalFanTotalRefinement route) := by
    rw [gridPolylineSegments_scalePolyline]
    exact List.mem_map_of_mem finalMember
  unfold retainedTerminalRefinedUnitPolyline
  apply
    unitSubdividedRasterizeRetainedSegment_point_mem_whole
      (retained.scale (by native_decide))
      scaledFinalMember
  simpa [finalSegment, GridSegment.scale] using
    retainedTerminalRefinedCheckpoint_mem_unitSubdividedFinalRasterization
      route terminal routeLength classified point checkpoint

/-- Disjoint canonical refined unit-grid routes imply the finite checkpoint
avoidance certificate required by mixed source-prefix/fan separation. -/
theorem
    sourcePrefixAvoidsRetainedTerminalRefinedCheckpoints_of_unitRoutesDisjoint
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
    (disjoint :
      ∀ point,
        point ∈ retainedTerminalRefinedUnitPolyline sourceRoute →
          point ∈
            retainedTerminalRefinedUnitPolyline referenceRoute →
          False) :
    SourcePrefixAvoidsRetainedTerminalRefinedCheckpoints
      sourceRoute referenceRoute referenceTerminal := by
  constructor
  · intro sourcePoint sourcePointMember checkpoint
    apply disjoint
      (Cell.scale retainedTerminalFanTotalRefinement sourcePoint)
    · exact
        scaledSourcePoint_mem_retainedTerminalRefinedUnitPolyline
          sourceRoute sourceRetained sourceLength sourcePoint
          (List.mem_of_mem_dropLast sourcePointMember)
    · exact
        retainedTerminalRefinedCheckpoint_mem_retainedTerminalRefinedUnitPolyline
          referenceRoute referenceTerminal referenceRetained
          referenceLength referenceClassified
          (Cell.scale retainedTerminalFanTotalRefinement sourcePoint)
          checkpoint
  · intro sourceSegment sourceSegmentMember checkpoint
    rcases checkpoint with
      ⟨index, indexBound, sourceContains⟩
    let checkpointPoint :=
      Cell.add
        (Cell.scale retainedTerminalFanTotalRefinement
          (referenceRoute.getLastD (0, 0)))
        (Cell.scale index referenceTerminal.1.primitive)
    have sourceOriginalMember :
        sourceSegment ∈ gridPolylineSegments sourceRoute :=
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.gridPolylineSegments_dropLast_subset
        sourceRoute sourceSegmentMember
    have sourceScaledMember :
        sourceSegment.scale retainedTerminalFanTotalRefinement ∈
          gridPolylineSegments
            (scalePolyline retainedTerminalFanTotalRefinement
              sourceRoute) := by
      rw [gridPolylineSegments_scalePolyline]
      exact List.mem_map_of_mem sourceOriginalMember
    apply disjoint checkpointPoint
    · unfold retainedTerminalRefinedUnitPolyline
      exact
        axisSegmentPoint_mem_unitSubdividedRasterizeRetainedPolyline
          (sourceRetained.scale (by native_decide))
          sourceScaledMember sourceContains
    · apply
        retainedTerminalRefinedCheckpoint_mem_retainedTerminalRefinedUnitPolyline
          referenceRoute referenceTerminal referenceRetained
          referenceLength referenceClassified
          checkpointPoint
      exact ⟨index, indexBound, rfl⟩

/-- The strong no-shared-unit-route-points invariant directly discharges the
remaining mixed source-prefix corridor premise. -/
theorem sourcePrefixCorridorSeparated_of_unitRoutesDisjoint
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
    (disjoint :
      ∀ point,
        point ∈ retainedTerminalRefinedUnitPolyline sourceRoute →
          point ∈
            retainedTerminalRefinedUnitPolyline referenceRoute →
          False) :
    SourcePrefixCorridorSeparated
      sourceRoute referenceRoute referenceTerminal.1 := by
  apply
    sourcePrefixCorridorSeparated_of_avoids_refinedCheckpoints
      sourceRoute referenceRoute referenceTerminal
      referenceLength referenceClassified
  exact
    sourcePrefixAvoidsRetainedTerminalRefinedCheckpoints_of_unitRoutesDisjoint
      sourceRoute referenceRoute referenceTerminal
      sourceRetained referenceRetained
      sourceLength referenceLength referenceClassified
      disjoint

end PeriodicEightOccurrenceSplit
end LeanTrominoes
