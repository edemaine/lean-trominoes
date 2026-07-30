import LeanTrominoes.OrthogonalPolylineStrictSeparation

/-!
# Linear separation of orthogonal polylines

Axis-aligned rectangles are convenient separation certificates but do not
separate two rays in adjacent angular sectors.  This file supplies the
corresponding half-plane certificate.  An integer linear functional bounds
every vertex of the first route above by a threshold and every vertex of
the second route strictly below by that threshold.

Because a linear functional takes every point of an axis-aligned segment
between its endpoint values, these vertex bounds exclude point contacts,
perpendicular crossings, and collinear open-interval overlap.
-/

namespace LeanTrominoes

/-- Integer linear functional with the given normal vector. -/
def Cell.linearValue (normal point : Cell) : Int :=
  normal.1 * point.1 + normal.2 * point.2

private theorem linear_le_of_between
    (coefficient fixed first last value bound : Int)
    (firstBound :
      coefficient * first + fixed ≤ bound)
    (lastBound :
      coefficient * last + fixed ≤ bound)
    (between : GridSegment.Between first last value) :
    coefficient * value + fixed ≤ bound := by
  rcases between with ⟨firstLe, valueLe⟩ |
      ⟨lastLe, valueLe⟩
  · by_cases coefficientNonnegative : 0 ≤ coefficient
    · have scaled :=
        mul_le_mul_of_nonneg_left valueLe
          coefficientNonnegative
      omega
    · have coefficientNonpositive : coefficient ≤ 0 :=
        le_of_not_ge coefficientNonnegative
      have scaled :=
        mul_le_mul_of_nonpos_left firstLe
          coefficientNonpositive
      omega
  · by_cases coefficientNonnegative : 0 ≤ coefficient
    · have scaled :=
        mul_le_mul_of_nonneg_left valueLe
          coefficientNonnegative
      omega
    · have coefficientNonpositive : coefficient ≤ 0 :=
        le_of_not_ge coefficientNonnegative
      have scaled :=
        mul_le_mul_of_nonpos_left lastLe
          coefficientNonpositive
      omega

private theorem linear_gt_of_between
    (coefficient fixed first last value bound : Int)
    (firstBound :
      bound < coefficient * first + fixed)
    (lastBound :
      bound < coefficient * last + fixed)
    (between : GridSegment.Between first last value) :
    bound < coefficient * value + fixed := by
  rcases between with ⟨firstLe, valueLe⟩ |
      ⟨lastLe, valueLe⟩
  · by_cases coefficientNonnegative : 0 ≤ coefficient
    · have scaled :=
        mul_le_mul_of_nonneg_left firstLe
          coefficientNonnegative
      omega
    · have coefficientNonpositive : coefficient ≤ 0 :=
        le_of_not_ge coefficientNonnegative
      have scaled :=
        mul_le_mul_of_nonpos_left valueLe
          coefficientNonpositive
      omega
  · by_cases coefficientNonnegative : 0 ≤ coefficient
    · have scaled :=
        mul_le_mul_of_nonneg_left lastLe
          coefficientNonnegative
      omega
    · have coefficientNonpositive : coefficient ≤ 0 :=
        le_of_not_ge coefficientNonnegative
      have scaled :=
        mul_le_mul_of_nonpos_left valueLe
          coefficientNonpositive
      omega

/-- A linear upper bound at both endpoints extends over every point on an
axis-aligned segment. -/
theorem Cell.linearValue_le_of_segment_contains
    (normal : Cell) (bound : Int)
    {segment : GridSegment} {point : Cell}
    (startBound :
      Cell.linearValue normal segment.start ≤ bound)
    (finishBound :
      Cell.linearValue normal segment.finish ≤ bound)
    (contains : segment.Contains point) :
    Cell.linearValue normal point ≤ bound := by
  rcases normal with ⟨normalX, normalY⟩
  rcases point with ⟨pointX, pointY⟩
  rcases segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  simp only [Cell.linearValue] at startBound finishBound ⊢
  simp only [GridSegment.Contains,
    GridSegment.IsHorizontal, GridSegment.IsVertical] at contains
  rcases contains with
      ⟨horizontal, pointY, between⟩ |
      ⟨vertical, pointX, between⟩
  · rw [pointY]
    rw [← horizontal.1] at finishBound
    exact linear_le_of_between
      normalX (normalY * startY)
      startX finishX pointX bound
      startBound finishBound between
  · rw [pointX]
    rw [← vertical.1] at finishBound
    simpa [add_comm] using
      (linear_le_of_between
        normalY (normalX * startX)
        startY finishY pointY bound
        (by simpa [add_comm] using startBound)
        (by simpa [add_comm] using finishBound)
        between)

/-- A strict linear lower bound at both endpoints extends over every point
on an axis-aligned segment. -/
theorem Cell.linearValue_gt_of_segment_contains
    (normal : Cell) (bound : Int)
    {segment : GridSegment} {point : Cell}
    (startBound :
      bound < Cell.linearValue normal segment.start)
    (finishBound :
      bound < Cell.linearValue normal segment.finish)
    (contains : segment.Contains point) :
    bound < Cell.linearValue normal point := by
  rcases normal with ⟨normalX, normalY⟩
  rcases point with ⟨pointX, pointY⟩
  rcases segment with
    ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  simp only [Cell.linearValue] at startBound finishBound ⊢
  simp only [GridSegment.Contains,
    GridSegment.IsHorizontal, GridSegment.IsVertical] at contains
  rcases contains with
      ⟨horizontal, pointY, between⟩ |
      ⟨vertical, pointX, between⟩
  · rw [pointY]
    rw [← horizontal.1] at finishBound
    exact linear_gt_of_between
      normalX (normalY * startY)
      startX finishX pointX bound
      startBound finishBound between
  · rw [pointX]
    rw [← vertical.1] at finishBound
    simpa [add_comm] using
      (linear_gt_of_between
        normalY (normalX * startX)
        startY finishY pointY bound
        (by simpa [add_comm] using startBound)
        (by simpa [add_comm] using finishBound)
        between)

private theorem openIntervalsOverlap_endpoint_between
    {firstStart firstFinish secondStart secondFinish : Int}
    (overlap :
      GridSegment.OpenIntervalsOverlap
        firstStart firstFinish secondStart secondFinish) :
    GridSegment.Between firstStart firstFinish secondStart ∨
      GridSegment.Between firstStart firstFinish secondFinish ∨
      GridSegment.Between secondStart secondFinish firstStart ∨
      GridSegment.Between secondStart secondFinish firstFinish := by
  rcases le_total firstStart firstFinish with
      firstForward | firstBackward <;>
    rcases le_total secondStart secondFinish with
      secondForward | secondBackward
  all_goals
    simp only [GridSegment.OpenIntervalsOverlap,
      GridSegment.Between] at overlap ⊢
  · rw [min_eq_left firstForward, max_eq_right firstForward,
      min_eq_left secondForward, max_eq_right secondForward]
      at overlap
    omega
  · rw [min_eq_left firstForward, max_eq_right firstForward,
      min_eq_right secondBackward, max_eq_left secondBackward]
      at overlap
    omega
  · rw [min_eq_right firstBackward, max_eq_left firstBackward,
      min_eq_left secondForward, max_eq_right secondForward]
      at overlap
    omega
  · rw [min_eq_right firstBackward, max_eq_left firstBackward,
      min_eq_right secondBackward, max_eq_left secondBackward]
      at overlap
    omega

/-- Axis-aligned segment interiors cannot meet when their endpoints lie on
strictly opposite sides of a linear threshold. -/
theorem Cell.not_interiorsMeet_of_linear_separated
    (normal : Cell) (bound : Int)
    {first second : GridSegment}
    (firstStart :
      Cell.linearValue normal first.start ≤ bound)
    (firstFinish :
      Cell.linearValue normal first.finish ≤ bound)
    (secondStart :
      bound < Cell.linearValue normal second.start)
    (secondFinish :
      bound < Cell.linearValue normal second.finish) :
    ¬GridSegment.InteriorsMeet first second := by
  intro meet
  rcases meet with
      horizontal | vertical |
      horizontalVertical | verticalHorizontal
  · rcases horizontal with
      ⟨firstHorizontal, secondHorizontal, sameLine, overlap⟩
    rcases openIntervalsOverlap_endpoint_between overlap with
        secondStartBetween | secondFinishBetween |
        firstStartBetween | firstFinishBetween
    · have contained : first.Contains second.start :=
        Or.inl
          ⟨firstHorizontal, sameLine.symm,
            secondStartBetween⟩
      have :=
        Cell.linearValue_le_of_segment_contains
          normal bound firstStart firstFinish contained
      omega
    · have contained : first.Contains second.finish :=
        Or.inl
          ⟨firstHorizontal,
            secondHorizontal.1.symm.trans sameLine.symm,
            secondFinishBetween⟩
      have :=
        Cell.linearValue_le_of_segment_contains
          normal bound firstStart firstFinish contained
      omega
    · have contained : second.Contains first.start :=
        Or.inl
          ⟨secondHorizontal, sameLine,
            firstStartBetween⟩
      have :=
        Cell.linearValue_gt_of_segment_contains
          normal bound secondStart secondFinish contained
      omega
    · have contained : second.Contains first.finish :=
        Or.inl
          ⟨secondHorizontal,
            firstHorizontal.1.symm.trans sameLine,
            firstFinishBetween⟩
      have :=
        Cell.linearValue_gt_of_segment_contains
          normal bound secondStart secondFinish contained
      omega
  · rcases vertical with
      ⟨firstVertical, secondVertical, sameLine, overlap⟩
    rcases openIntervalsOverlap_endpoint_between overlap with
        secondStartBetween | secondFinishBetween |
        firstStartBetween | firstFinishBetween
    · have contained : first.Contains second.start :=
        Or.inr
          ⟨firstVertical, sameLine.symm,
            secondStartBetween⟩
      have :=
        Cell.linearValue_le_of_segment_contains
          normal bound firstStart firstFinish contained
      omega
    · have contained : first.Contains second.finish :=
        Or.inr
          ⟨firstVertical,
            secondVertical.1.symm.trans sameLine.symm,
            secondFinishBetween⟩
      have :=
        Cell.linearValue_le_of_segment_contains
          normal bound firstStart firstFinish contained
      omega
    · have contained : second.Contains first.start :=
        Or.inr
          ⟨secondVertical, sameLine,
            firstStartBetween⟩
      have :=
        Cell.linearValue_gt_of_segment_contains
          normal bound secondStart secondFinish contained
      omega
    · have contained : second.Contains first.finish :=
        Or.inr
          ⟨secondVertical,
            firstVertical.1.symm.trans sameLine,
            firstFinishBetween⟩
      have :=
        Cell.linearValue_gt_of_segment_contains
          normal bound secondStart secondFinish contained
      omega
  · rcases horizontalVertical with
      ⟨firstHorizontal, secondVertical,
        firstBetween, secondBetween⟩
    let intersection : Cell :=
      (second.start.1, first.start.2)
    have firstContains : first.Contains intersection :=
      GridSegment.contains_of_interiorContains
        (Or.inl
          ⟨firstHorizontal, rfl, firstBetween⟩)
    have secondContains : second.Contains intersection :=
      GridSegment.contains_of_interiorContains
        (Or.inr
          ⟨secondVertical, rfl, secondBetween⟩)
    have intersectionLe :=
      Cell.linearValue_le_of_segment_contains
        normal bound firstStart firstFinish firstContains
    have intersectionGt :=
      Cell.linearValue_gt_of_segment_contains
        normal bound secondStart secondFinish secondContains
    omega
  · rcases verticalHorizontal with
      ⟨firstVertical, secondHorizontal,
        secondBetween, firstBetween⟩
    let intersection : Cell :=
      (first.start.1, second.start.2)
    have firstContains : first.Contains intersection :=
      GridSegment.contains_of_interiorContains
        (Or.inr
          ⟨firstVertical, rfl, firstBetween⟩)
    have secondContains : second.Contains intersection :=
      GridSegment.contains_of_interiorContains
        (Or.inl
          ⟨secondHorizontal, rfl, secondBetween⟩)
    have intersectionLe :=
      Cell.linearValue_le_of_segment_contains
        normal bound firstStart firstFinish firstContains
    have intersectionGt :=
      Cell.linearValue_gt_of_segment_contains
        normal bound secondStart secondFinish secondContains
    omega

/-- Pointwise strict half-plane bounds give complete contact-free
continuous separation of two finite orthogonal routes. -/
theorem routesStrictlyAvoidEachOther_of_linear_separated
    (normal : Cell) (bound : Int)
    {first second : List Cell}
    (firstBounded :
      ∀ point ∈ first,
        Cell.linearValue normal point ≤ bound)
    (secondBounded :
      ∀ point ∈ second,
        bound < Cell.linearValue normal point) :
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther
      first second := by
  unfold
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro firstSegment firstMember secondSegment secondMember
    have firstEndpoints :=
      gridPolylineSegments_endpoints_mem firstMember
    have secondEndpoints :=
      gridPolylineSegments_endpoints_mem secondMember
    exact Cell.not_interiorsMeet_of_linear_separated
      normal bound
      (firstBounded _ firstEndpoints.1)
      (firstBounded _ firstEndpoints.2)
      (secondBounded _ secondEndpoints.1)
      (secondBounded _ secondEndpoints.2)
  · intro firstPoint firstPointMember
      secondSegment secondSegmentMember
    have secondEndpoints :=
      gridPolylineSegments_endpoints_mem secondSegmentMember
    intro interior
    have contains :=
      GridSegment.contains_of_interiorContains interior
    have pointGt :=
      Cell.linearValue_gt_of_segment_contains
        normal bound
        (secondBounded _ secondEndpoints.1)
        (secondBounded _ secondEndpoints.2)
        contains
    exact (not_lt_of_ge
      (firstBounded _ firstPointMember)) pointGt
  · intro secondPoint secondPointMember
      firstSegment firstSegmentMember
    have firstEndpoints :=
      gridPolylineSegments_endpoints_mem firstSegmentMember
    intro interior
    have contains :=
      GridSegment.contains_of_interiorContains interior
    have pointLe :=
      Cell.linearValue_le_of_segment_contains
        normal bound
        (firstBounded _ firstEndpoints.1)
        (firstBounded _ firstEndpoints.2)
        contains
    exact (not_lt_of_ge pointLe)
      (secondBounded _ secondPointMember)
  · intro firstPoint firstPointMember
      secondPoint secondPointMember equal
    subst secondPoint
    exact (not_lt_of_ge
      (firstBounded _ firstPointMember))
      (secondBounded _ secondPointMember)

end LeanTrominoes
