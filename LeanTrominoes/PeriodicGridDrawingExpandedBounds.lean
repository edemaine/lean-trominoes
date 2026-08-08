import LeanTrominoes.PeriodicGridDrawingFiniteContinuousPlanarity

/-!
# Finite periodic checks with one-cell endpoint halos

A stored route for an edge with nonzero periodic offset necessarily ends
outside the canonical fundamental square.  The strict endpoint hypothesis of
the original nine-neighbor checker is therefore too strong for general local
periodic graphs.

This file develops the correct bounded setting used by the hardness
construction: every stored segment endpoint lies in the `3 × 3` halo
`(-P, 2P)²` around a fundamental square of side `P`.  Contacts between two
such stored routes can differ by at most two period translations in each
coordinate, giving a finite `5 × 5` relative-translation set.
-/

namespace LeanTrominoes
namespace PeriodicGridDrawing

/-- A point lies in the open one-cell halo around the fundamental square. -/
def PositionInExpandedSquare
    (drawing : PeriodicGridDrawing) (position : Cell) : Prop :=
  -(drawing.gridSize : Int) < position.1 ∧
    position.1 < 2 * drawing.gridSize ∧
    -(drawing.gridSize : Int) < position.2 ∧
    position.2 < 2 * drawing.gridSize

/-- A halo point with one additional unit of room below the upper boundary
in each coordinate.  This is the exact margin needed by the canonical
`max + 1` Manhattan detour. -/
def PositionInExpandedSquareWithUpperMargin
    (drawing : PeriodicGridDrawing) (position : Cell) : Prop :=
  -(drawing.gridSize : Int) < position.1 ∧
    position.1 + 1 < 2 * drawing.gridSize ∧
    -(drawing.gridSize : Int) < position.2 ∧
    position.2 + 1 < 2 * drawing.gridSize

/-- Forgetting the extra unit of upper margin recovers ordinary halo
membership. -/
theorem positionInExpandedSquare_of_upperMargin
    {drawing : PeriodicGridDrawing} {position : Cell}
    (inside :
      drawing.PositionInExpandedSquareWithUpperMargin position) :
    drawing.PositionInExpandedSquare position := by
  simp only [PositionInExpandedSquareWithUpperMargin] at inside
  simp only [PositionInExpandedSquare]
  omega

/-- Every stored segment endpoint lies in the open one-cell halo. -/
def SegmentEndpointsInExpandedSquare
    (drawing : PeriodicGridDrawing) : Prop :=
  ∀ indexed ∈ drawing.indexedSegments,
    drawing.PositionInExpandedSquare indexed.segment.start ∧
      drawing.PositionInExpandedSquare indexed.segment.finish

/-- The canonical open fundamental square is contained in its one-cell
halo. -/
theorem positionInExpandedSquare_of_fundamental
    {drawing : PeriodicGridDrawing} {position : Cell}
    (inside : drawing.PositionInFundamentalSquare position) :
    drawing.PositionInExpandedSquare position := by
  simp only [PositionInFundamentalSquare] at inside
  simp only [PositionInExpandedSquare]
  have periodPositive : (0 : Int) < drawing.gridSize := by
    exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  omega

/-- Fundamental-square points have the one-unit upper margin needed by the
canonical detour, because the positive period leaves an entire neighboring
cell above them. -/
theorem positionInExpandedSquareWithUpperMargin_of_fundamental
    {drawing : PeriodicGridDrawing} {position : Cell}
    (inside : drawing.PositionInFundamentalSquare position) :
    drawing.PositionInExpandedSquareWithUpperMargin position := by
  simp only [PositionInFundamentalSquare] at inside
  simp only [PositionInExpandedSquareWithUpperMargin]
  have periodPositive : (0 : Int) < drawing.gridSize := by
    exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  omega

/-- The five possible coordinates of a relative translation between two
halo-bounded segment occurrences that meet. -/
def doubleNeighborCoordinates : List Int :=
  [-2, -1, 0, 1, 2]

/-- The `5 × 5` relative-translation set for two halo-bounded routes. -/
def doubleNeighborTranslations : List Cell :=
  doubleNeighborCoordinates.flatMap fun horizontal =>
    doubleNeighborCoordinates.map fun vertical =>
      (horizontal, vertical)

@[simp]
theorem mem_doubleNeighborCoordinates_iff (coordinate : Int) :
    coordinate ∈ doubleNeighborCoordinates ↔
      -2 ≤ coordinate ∧ coordinate ≤ 2 := by
  simp [doubleNeighborCoordinates]
  omega

@[simp]
theorem mem_doubleNeighborTranslations_iff (translate : Cell) :
    translate ∈ doubleNeighborTranslations ↔
      (-2 ≤ translate.1 ∧ translate.1 ≤ 2) ∧
        (-2 ≤ translate.2 ∧ translate.2 ≤ 2) := by
  rcases translate with ⟨horizontal, vertical⟩
  simp [doubleNeighborTranslations]

theorem doubleNeighborCoordinates_nodup :
    doubleNeighborCoordinates.Nodup := by
  decide

theorem doubleNeighborTranslations_nodup :
    doubleNeighborTranslations.Nodup := by
  native_decide

/-- The `5 × 5` relative-translation set is closed under negation. -/
theorem sub_zero_mem_doubleNeighborTranslations_iff (translate : Cell) :
    Cell.sub (0, 0) translate ∈ doubleNeighborTranslations ↔
      translate ∈ doubleNeighborTranslations := by
  rcases translate with ⟨horizontal, vertical⟩
  simp only [mem_doubleNeighborTranslations_iff, Cell.sub]
  omega

/-- Equality of a translated halo coordinate with another halo coordinate
bounds the relative period shift by two. -/
theorem lane_shift_is_doubleNeighbor
    {period first second shift : Int}
    (periodPositive : 0 < period)
    (firstLower : -period < first)
    (firstUpper : first < 2 * period)
    (secondLower : -period < second)
    (secondUpper : second < 2 * period)
    (equal : second = first + period * shift) :
    -2 ≤ shift ∧ shift ≤ 2 := by
  constructor
  · by_contra tooLow
    have shiftLow : shift ≤ -3 := by omega
    have nonnegative :
        0 ≤ period * (-shift - 3) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productUpper :
        period * shift ≤ -3 * period := by
      nlinarith
    omega
  · by_contra tooHigh
    have shiftHigh : 3 ≤ shift := by omega
    have nonnegative :
        0 ≤ period * (shift - 3) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productLower :
        3 * period ≤ period * shift := by
      nlinarith
    omega

/-- Strict betweenness between translated halo endpoints and a halo point
has the same relative-shift bound. -/
theorem between_shift_is_doubleNeighbor
    {period first finish shift point : Int}
    (periodPositive : 0 < period)
    (firstLower : -period < first)
    (firstUpper : first < 2 * period)
    (finishLower : -period < finish)
    (finishUpper : finish < 2 * period)
    (pointLower : -period < point)
    (pointUpper : point < 2 * period)
    (between :
      GridSegment.StrictlyBetween
        (first + period * shift)
        (finish + period * shift) point) :
    -2 ≤ shift ∧ shift ≤ 2 := by
  constructor
  · by_contra tooLow
    have shiftLow : shift ≤ -3 := by omega
    have nonnegative :
        0 ≤ period * (-shift - 3) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productUpper :
        period * shift ≤ -3 * period := by
      nlinarith
    unfold GridSegment.StrictlyBetween at between
    rcases between with between | between <;> omega
  · by_contra tooHigh
    have shiftHigh : 3 ≤ shift := by omega
    have nonnegative :
        0 ≤ period * (shift - 3) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productLower :
        3 * period ≤ period * shift := by
      nlinarith
    unfold GridSegment.StrictlyBetween at between
    rcases between with between | between <;> omega

/-- Closed containment in a halo-bounded segment keeps the contained point
inside the same halo. -/
theorem expanded_of_contains
    {drawing : PeriodicGridDrawing}
    {segment : GridSegment} {point : Cell}
    (startBounds :
      drawing.PositionInExpandedSquare segment.start)
    (finishBounds :
      drawing.PositionInExpandedSquare segment.finish)
    (contains : segment.Contains point) :
    drawing.PositionInExpandedSquare point := by
  rcases startBounds with
    ⟨startXLower, startXUpper, startYLower, startYUpper⟩
  rcases finishBounds with
    ⟨finishXLower, finishXUpper, finishYLower, finishYUpper⟩
  rcases contains with
    ⟨horizontal, same, between⟩ |
      ⟨vertical, same, between⟩
  · rcases between with between | between <;>
      simp only [GridSegment.IsHorizontal] at horizontal <;>
      simp only [PositionInExpandedSquare] <;>
      omega
  · rcases between with between | between <;>
      simp only [GridSegment.IsVertical] at vertical <;>
      simp only [PositionInExpandedSquare] <;>
      omega

/-- Closed containment in a segment whose endpoints have one unit of upper
halo margin preserves that margin. -/
theorem expandedWithUpperMargin_of_contains
    {drawing : PeriodicGridDrawing}
    {segment : GridSegment} {point : Cell}
    (startBounds :
      drawing.PositionInExpandedSquareWithUpperMargin segment.start)
    (finishBounds :
      drawing.PositionInExpandedSquareWithUpperMargin segment.finish)
    (contains : segment.Contains point) :
    drawing.PositionInExpandedSquareWithUpperMargin point := by
  rcases startBounds with
    ⟨startXLower, startXUpper, startYLower, startYUpper⟩
  rcases finishBounds with
    ⟨finishXLower, finishXUpper, finishYLower, finishYUpper⟩
  rcases contains with
    ⟨horizontal, same, between⟩ |
      ⟨vertical, same, between⟩
  · rcases between with between | between <;>
      simp only [GridSegment.IsHorizontal] at horizontal <;>
      simp only [PositionInExpandedSquareWithUpperMargin] <;>
      omega
  · rcases between with between | between <;>
      simp only [GridSegment.IsVertical] at vertical <;>
      simp only [PositionInExpandedSquareWithUpperMargin] <;>
      omega

/-- A contact between two halo-bounded segment occurrences has relative
translation in the finite `5 × 5` set. -/
theorem relativeTranslate_isDoubleNeighbor_of_contact
    {drawing : PeriodicGridDrawing}
    (endpointBounds : drawing.SegmentEndpointsInExpandedSquare)
    {first second : IndexedGridSegment}
    (firstMember : first ∈ drawing.indexedSegments)
    (secondMember : second ∈ drawing.indexedSegments)
    {firstTranslate secondTranslate point : Cell}
    (firstContains :
      (first.segment.translate
        (drawing.periodTranslation firstTranslate)).InteriorContains point)
    (secondContains :
      (second.segment.translate
        (drawing.periodTranslation secondTranslate)).Contains point) :
    Cell.sub firstTranslate secondTranslate ∈
      doubleNeighborTranslations := by
  let relative := Cell.sub firstTranslate secondTranslate
  let normalized := drawing.normalizePoint point secondTranslate
  have normalizedFirst :
      (first.segment.translate
        (drawing.periodTranslation relative)).InteriorContains normalized :=
    (interiorContains_normalize drawing first.segment
      firstTranslate secondTranslate point).mp firstContains
  have normalizedSecond : second.segment.Contains normalized := by
    simpa [Cell.sub, periodTranslation, Cell.scale,
      GridSegment.translate, Cell.add] using
      (contains_normalize drawing second.segment
        secondTranslate secondTranslate point).mp secondContains
  have normalizedBounds :
      drawing.PositionInExpandedSquare normalized :=
    expanded_of_contains
      (endpointBounds second secondMember).1
      (endpointBounds second secondMember).2
      normalizedSecond
  have periodPositive : (0 : Int) < drawing.gridSize := by
    exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have firstBounds := endpointBounds first firstMember
  apply (mem_doubleNeighborTranslations_iff relative).mpr
  rcases firstBounds with ⟨startBounds, finishBounds⟩
  rcases startBounds with
    ⟨startXLower, startXUpper, startYLower, startYUpper⟩
  rcases finishBounds with
    ⟨finishXLower, finishXUpper, finishYLower, finishYUpper⟩
  rcases normalizedBounds with
    ⟨pointXLower, pointXUpper, pointYLower, pointYUpper⟩
  rcases normalizedFirst with
    ⟨horizontal, same, between⟩ |
      ⟨vertical, same, between⟩
  · have same' :
        normalized.2 =
          first.segment.start.2 +
            drawing.gridSize * relative.2 := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using same
    have between' :
        GridSegment.StrictlyBetween
          (first.segment.start.1 +
            drawing.gridSize * relative.1)
          (first.segment.finish.1 +
            drawing.gridSize * relative.1)
          normalized.1 := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using between
    exact
      ⟨between_shift_is_doubleNeighbor periodPositive
          startXLower startXUpper finishXLower finishXUpper
          pointXLower pointXUpper between',
        lane_shift_is_doubleNeighbor periodPositive
          startYLower startYUpper
          pointYLower pointYUpper same'⟩
  · have same' :
        normalized.1 =
          first.segment.start.1 +
            drawing.gridSize * relative.1 := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using same
    have between' :
        GridSegment.StrictlyBetween
          (first.segment.start.2 +
            drawing.gridSize * relative.2)
          (first.segment.finish.2 +
            drawing.gridSize * relative.2)
          normalized.2 := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using between
    exact
      ⟨lane_shift_is_doubleNeighbor periodPositive
          startXLower startXUpper
          pointXLower pointXUpper same',
        between_shift_is_doubleNeighbor periodPositive
          startYLower startYUpper finishYLower finishYUpper
          pointYLower pointYUpper between'⟩

/-- A translated halo-bounded segment meeting a translated halo-bounded
point also has one of the `5 × 5` relative translations. -/
theorem relativeTranslate_isDoubleNeighbor_of_expandedPointContact
    {drawing : PeriodicGridDrawing}
    (endpointBounds : drawing.SegmentEndpointsInExpandedSquare)
    {point : Cell}
    (pointBounds : drawing.PositionInExpandedSquare point)
    {indexed : IndexedGridSegment}
    (indexedMember : indexed ∈ drawing.indexedSegments)
    {pointTranslate routeTranslate : Cell}
    (contains :
      (indexed.segment.translate
        (drawing.periodTranslation routeTranslate)).InteriorContains
        (Cell.add point
          (drawing.periodTranslation pointTranslate))) :
    Cell.sub routeTranslate pointTranslate ∈
      doubleNeighborTranslations := by
  let relative := Cell.sub routeTranslate pointTranslate
  have normalized :
      (indexed.segment.translate
        (drawing.periodTranslation relative)).InteriorContains point := by
    have := (interiorContains_normalize drawing indexed.segment
      routeTranslate pointTranslate
      (Cell.add point
        (drawing.periodTranslation pointTranslate))).mp contains
    simpa [relative, normalizePoint, Cell.add, Cell.sub] using this
  have periodPositive : (0 : Int) < drawing.gridSize := by
    exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have segmentBounds := endpointBounds indexed indexedMember
  apply (mem_doubleNeighborTranslations_iff relative).mpr
  rcases segmentBounds with ⟨startBounds, finishBounds⟩
  rcases startBounds with
    ⟨startXLower, startXUpper, startYLower, startYUpper⟩
  rcases finishBounds with
    ⟨finishXLower, finishXUpper, finishYLower, finishYUpper⟩
  rcases pointBounds with
    ⟨pointXLower, pointXUpper, pointYLower, pointYUpper⟩
  rcases normalized with
    ⟨horizontal, same, between⟩ |
      ⟨vertical, same, between⟩
  · have same' :
        point.2 =
          indexed.segment.start.2 +
            drawing.gridSize * relative.2 := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using same
    have between' :
        GridSegment.StrictlyBetween
          (indexed.segment.start.1 +
            drawing.gridSize * relative.1)
          (indexed.segment.finish.1 +
            drawing.gridSize * relative.1)
          point.1 := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using between
    exact
      ⟨between_shift_is_doubleNeighbor periodPositive
          startXLower startXUpper finishXLower finishXUpper
          pointXLower pointXUpper between',
        lane_shift_is_doubleNeighbor periodPositive
          startYLower startYUpper
          pointYLower pointYUpper same'⟩
  · have same' :
        point.1 =
          indexed.segment.start.1 +
            drawing.gridSize * relative.1 := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using same
    have between' :
        GridSegment.StrictlyBetween
          (indexed.segment.start.2 +
            drawing.gridSize * relative.2)
          (indexed.segment.finish.2 +
            drawing.gridSize * relative.2)
          point.2 := by
      simpa [GridSegment.translate, periodTranslation,
        Cell.add, Cell.scale, add_comm] using between
    exact
      ⟨lane_shift_is_doubleNeighbor periodPositive
          startXLower startXUpper
          pointXLower pointXUpper same',
        between_shift_is_doubleNeighbor periodPositive
          startYLower startYUpper finishYLower finishYUpper
          pointYLower pointYUpper between'⟩

end PeriodicGridDrawing
end LeanTrominoes
