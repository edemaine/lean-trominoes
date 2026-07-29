import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierNoncarrierPeriodicSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierAnchorGeometry

/-!
# Reducing carrier--noncarrier contact to finite-halo closure

A selected carrier source is already a neighboring raw retained link.  To
compare it with an arbitrary final noncarrier occurrence, keep that carrier
source fixed and translate the noncarrier source by the difference of their
physical shifts.  Both resulting finite routes then use the carrier's physical
shift as their common external translate.

Consequently, periodic carrier--noncarrier separation is reduced to one
geometric closure fact: if the two final segments met, the translated
noncarrier source would still belong to the retained finite halo.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- A fundamental coordinate plus an integral period translate can lie in
the half-open three-cell window `[-P, 2P)` only for shifts `-1`, `0`, or
`1`. -/
theorem fundamental_translate_shift_is_neighbor
    {period base shift lifted : Int}
    (periodPositive : 0 < period)
    (basePositive : 0 < base)
    (baseUpper : base < period)
    (liftedLower : -period ≤ lifted)
    (liftedUpper : lifted < 2 * period)
    (liftedEq : lifted = base + period * shift) :
    shift = -1 ∨ shift = 0 ∨ shift = 1 := by
  have notTooLow : ¬shift ≤ -2 := by
    intro shiftLow
    have nonnegative :
        0 ≤ period * (-shift - 2) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productUpper : period * shift ≤ -2 * period := by
      nlinarith
    omega
  have notTooHigh : ¬2 ≤ shift := by
    intro shiftHigh
    have nonnegative :
        0 ≤ period * (shift - 2) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productLower : 2 * period ≤ period * shift := by
      nlinarith
    omega
  omega

/-- Any integral displacement of at most two cells can be split between two
neighboring representatives.  This is the one-dimensional balancing fact
behind moving both sides of a periodic contact into the retained halo. -/
theorem exists_neighbor_coordinates_of_difference_le_two
    {difference : Int}
    (lower : -2 ≤ difference)
    (upper : difference ≤ 2) :
    ∃ first second : Int,
      (first = -1 ∨ first = 0 ∨ first = 1) ∧
        (second = -1 ∨ second = 0 ∨ second = 1) ∧
        first - second = difference := by
  have possibilities :
      difference = -2 ∨ difference = -1 ∨ difference = 0 ∨
        difference = 1 ∨ difference = 2 := by
    omega
  rcases possibilities with
      differenceEq | differenceEq | differenceEq |
        differenceEq | differenceEq
  · exact ⟨-1, 1, by simp, by simp, by omega⟩
  · exact ⟨-1, 0, by simp, by simp, by omega⟩
  · exact ⟨0, 0, by simp, by simp, by omega⟩
  · exact ⟨1, 0, by simp, by simp, by omega⟩
  · exact ⟨1, -1, by simp, by simp, by omega⟩

/-- Three coordinates with pairwise displacement at most two can be placed
simultaneously in the neighboring interval while preserving both
displacements from the first coordinate. -/
theorem exists_three_neighbor_coordinates_of_pairwise_difference_le_two
    {firstSecond firstThird : Int}
    (firstSecondLower : -2 ≤ firstSecond)
    (firstSecondUpper : firstSecond ≤ 2)
    (firstThirdLower : -2 ≤ firstThird)
    (firstThirdUpper : firstThird ≤ 2)
    (secondThirdLower : -2 ≤ firstThird - firstSecond)
    (secondThirdUpper : firstThird - firstSecond ≤ 2) :
    ∃ first second third : Int,
      (first = -1 ∨ first = 0 ∨ first = 1) ∧
        (second = -1 ∨ second = 0 ∨ second = 1) ∧
        (third = -1 ∨ third = 0 ∨ third = 1) ∧
        first - second = firstSecond ∧
        first - third = firstThird := by
  let first :=
    max (-1) (max (firstSecond - 1) (firstThird - 1))
  let second := first - firstSecond
  let third := first - firstThird
  refine ⟨first, second, third, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [first, second, third, max_def]
    split_ifs <;> omega

/-- If two source coordinates differ by at most two lattice cells after
physical alignment, their source shifts can be adjusted while preserving
that alignment so that both translated source coordinates are neighboring.

The returned equation is oriented for a common external translate:
`firstAdjustment - secondAdjustment = relative`. -/
theorem exists_neighbor_balancing_adjustments
    (firstBase secondBase relative : Cell)
    (close :
      Cell.sub (Cell.add firstBase relative) secondBase ∈
        PeriodicGridDrawing.doubleNeighborTranslations) :
    ∃ firstAdjustment secondAdjustment : Cell,
      Cell.sub firstAdjustment secondAdjustment = relative ∧
        IsNeighborTranslation
          (Cell.add firstBase firstAdjustment) ∧
        IsNeighborTranslation
          (Cell.add secondBase secondAdjustment) := by
  have closeBounds :=
    (PeriodicGridDrawing.mem_doubleNeighborTranslations_iff
      (Cell.sub (Cell.add firstBase relative) secondBase)).mp close
  rcases
      exists_neighbor_coordinates_of_difference_le_two
        closeBounds.1.1 closeBounds.1.2 with
    ⟨firstX, secondX, firstXNeighbor, secondXNeighbor,
      horizontalDifference⟩
  rcases
      exists_neighbor_coordinates_of_difference_le_two
        closeBounds.2.1 closeBounds.2.2 with
    ⟨firstY, secondY, firstYNeighbor, secondYNeighbor,
      verticalDifference⟩
  let firstTarget : Cell := (firstX, firstY)
  let secondTarget : Cell := (secondX, secondY)
  let firstAdjustment := Cell.sub firstTarget firstBase
  let secondAdjustment := Cell.sub secondTarget secondBase
  refine ⟨firstAdjustment, secondAdjustment, ?_, ?_, ?_⟩
  · rcases firstBase with ⟨firstBaseX, firstBaseY⟩
    rcases secondBase with ⟨secondBaseX, secondBaseY⟩
    rcases relative with ⟨relativeX, relativeY⟩
    simp only [firstAdjustment, secondAdjustment, firstTarget,
      secondTarget, Cell.sub, Cell.add, Prod.mk.injEq] at horizontalDifference verticalDifference ⊢
    constructor <;> omega
  · simpa [firstAdjustment, firstTarget, Cell.add, Cell.sub,
      IsNeighborTranslation] using
        And.intro firstXNeighbor firstYNeighbor
  · simpa [secondAdjustment, secondTarget, Cell.add, Cell.sub,
      IsNeighborTranslation] using
        And.intro secondXNeighbor secondYNeighbor

/-- The two-coordinate version of source balancing.  One adjustment is
shared by two noncarrier occurrence coordinates, as required by a crossover
record's horizontal and vertical source occurrences. -/
theorem exists_neighbor_balancing_adjustments_two_second_bases
    (firstBase secondBase thirdBase relative : Cell)
    (firstSecondClose :
      Cell.sub (Cell.add firstBase relative) secondBase ∈
        PeriodicGridDrawing.doubleNeighborTranslations)
    (firstThirdClose :
      Cell.sub (Cell.add firstBase relative) thirdBase ∈
        PeriodicGridDrawing.doubleNeighborTranslations)
    (secondThirdClose :
      Cell.sub secondBase thirdBase ∈
        PeriodicGridDrawing.doubleNeighborTranslations) :
    ∃ firstAdjustment secondAdjustment : Cell,
      Cell.sub firstAdjustment secondAdjustment = relative ∧
        IsNeighborTranslation
          (Cell.add firstBase firstAdjustment) ∧
        IsNeighborTranslation
          (Cell.add secondBase secondAdjustment) ∧
        IsNeighborTranslation
          (Cell.add thirdBase secondAdjustment) := by
  have firstSecondBounds :=
    (PeriodicGridDrawing.mem_doubleNeighborTranslations_iff
      (Cell.sub (Cell.add firstBase relative) secondBase)).mp
      firstSecondClose
  have firstThirdBounds :=
    (PeriodicGridDrawing.mem_doubleNeighborTranslations_iff
      (Cell.sub (Cell.add firstBase relative) thirdBase)).mp
      firstThirdClose
  have secondThirdBounds :=
    (PeriodicGridDrawing.mem_doubleNeighborTranslations_iff
      (Cell.sub secondBase thirdBase)).mp secondThirdClose
  rcases
      exists_three_neighbor_coordinates_of_pairwise_difference_le_two
        firstSecondBounds.1.1 firstSecondBounds.1.2
        firstThirdBounds.1.1 firstThirdBounds.1.2
        (by
          rcases firstBase with ⟨firstBaseX, firstBaseY⟩
          rcases secondBase with ⟨secondBaseX, secondBaseY⟩
          rcases thirdBase with ⟨thirdBaseX, thirdBaseY⟩
          rcases relative with ⟨relativeX, relativeY⟩
          simp only [Cell.sub, Cell.add] at firstSecondBounds firstThirdBounds secondThirdBounds ⊢
          omega)
        (by
          rcases firstBase with ⟨firstBaseX, firstBaseY⟩
          rcases secondBase with ⟨secondBaseX, secondBaseY⟩
          rcases thirdBase with ⟨thirdBaseX, thirdBaseY⟩
          rcases relative with ⟨relativeX, relativeY⟩
          simp only [Cell.sub, Cell.add] at firstSecondBounds firstThirdBounds secondThirdBounds ⊢
          omega) with
    ⟨firstX, secondX, thirdX,
      firstXNeighbor, secondXNeighbor, thirdXNeighbor,
      firstSecondX, firstThirdX⟩
  rcases
      exists_three_neighbor_coordinates_of_pairwise_difference_le_two
        firstSecondBounds.2.1 firstSecondBounds.2.2
        firstThirdBounds.2.1 firstThirdBounds.2.2
        (by
          rcases firstBase with ⟨firstBaseX, firstBaseY⟩
          rcases secondBase with ⟨secondBaseX, secondBaseY⟩
          rcases thirdBase with ⟨thirdBaseX, thirdBaseY⟩
          rcases relative with ⟨relativeX, relativeY⟩
          simp only [Cell.sub, Cell.add] at firstSecondBounds firstThirdBounds secondThirdBounds ⊢
          omega)
        (by
          rcases firstBase with ⟨firstBaseX, firstBaseY⟩
          rcases secondBase with ⟨secondBaseX, secondBaseY⟩
          rcases thirdBase with ⟨thirdBaseX, thirdBaseY⟩
          rcases relative with ⟨relativeX, relativeY⟩
          simp only [Cell.sub, Cell.add] at firstSecondBounds firstThirdBounds secondThirdBounds ⊢
          omega) with
    ⟨firstY, secondY, thirdY,
      firstYNeighbor, secondYNeighbor, thirdYNeighbor,
      firstSecondY, firstThirdY⟩
  let firstTarget : Cell := (firstX, firstY)
  let secondTarget : Cell := (secondX, secondY)
  let firstAdjustment := Cell.sub firstTarget firstBase
  let secondAdjustment := Cell.sub secondTarget secondBase
  refine
    ⟨firstAdjustment, secondAdjustment, ?_, ?_, ?_, ?_⟩
  · rcases firstBase with ⟨firstBaseX, firstBaseY⟩
    rcases secondBase with ⟨secondBaseX, secondBaseY⟩
    rcases relative with ⟨relativeX, relativeY⟩
    simp only [firstAdjustment, secondAdjustment,
      firstTarget, secondTarget, Cell.sub, Cell.add,
      Prod.mk.injEq] at firstSecondX firstSecondY ⊢
    constructor <;> omega
  · simpa [firstAdjustment, firstTarget, Cell.add,
      Cell.sub, IsNeighborTranslation] using
        And.intro firstXNeighbor firstYNeighbor
  · simpa [secondAdjustment, secondTarget, Cell.add,
      Cell.sub, IsNeighborTranslation] using
        And.intro secondXNeighbor secondYNeighbor
  · have thirdTargetEq :
        Cell.add thirdBase secondAdjustment =
          (thirdX, thirdY) := by
      rcases firstBase with ⟨firstBaseX, firstBaseY⟩
      rcases secondBase with ⟨secondBaseX, secondBaseY⟩
      rcases thirdBase with ⟨thirdBaseX, thirdBaseY⟩
      rcases relative with ⟨relativeX, relativeY⟩
      simp only [secondAdjustment, secondTarget,
        Cell.sub, Cell.add, Prod.mk.injEq] at firstSecondX firstThirdX firstSecondY firstThirdY ⊢
      constructor <;> omega
    rw [thirdTargetEq]
    exact ⟨thirdXNeighbor, thirdYNeighbor⟩

/-- The sum of two neighboring lattice translations belongs to the
twenty-five-element doubled halo. -/
theorem IsNeighborTranslation.add_mem_doubleNeighborTranslations
    {first second : Cell}
    (firstNeighbor : IsNeighborTranslation first)
    (secondNeighbor : IsNeighborTranslation second) :
    Cell.add first second ∈
      PeriodicGridDrawing.doubleNeighborTranslations := by
  apply
    (PeriodicGridDrawing.mem_doubleNeighborTranslations_iff
      (Cell.add first second)).mpr
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [IsNeighborTranslation, Cell.add] at firstNeighbor secondNeighbor ⊢
  omega

/-- The difference of two neighboring lattice translations belongs to the
twenty-five-element doubled halo. -/
theorem IsNeighborTranslation.sub_mem_doubleNeighborTranslations
    {first second : Cell}
    (firstNeighbor : IsNeighborTranslation first)
    (secondNeighbor : IsNeighborTranslation second) :
    Cell.sub first second ∈
      PeriodicGridDrawing.doubleNeighborTranslations := by
  apply
    (PeriodicGridDrawing.mem_doubleNeighborTranslations_iff
      (Cell.sub first second)).mpr
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [IsNeighborTranslation, Cell.sub] at firstNeighbor secondNeighbor ⊢
  omega

/-- Closed betweenness between translated halo endpoints and a halo point
also bounds the translation coordinate by two. -/
theorem between_closed_shift_is_doubleNeighbor
    {period first finish shift point : Int}
    (periodPositive : 0 < period)
    (firstLower : -period < first)
    (firstUpper : first < 2 * period)
    (finishLower : -period < finish)
    (finishUpper : finish < 2 * period)
    (pointLower : -period < point)
    (pointUpper : point < 2 * period)
    (between :
      GridSegment.Between
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
    unfold GridSegment.Between at between
    rcases between with between | between <;> omega
  · by_contra tooHigh
    have shiftHigh : 3 ≤ shift := by omega
    have nonnegative :
        0 ≤ period * (shift - 3) :=
      mul_nonneg (le_of_lt periodPositive) (by omega)
    have productLower :
        3 * period ≤ period * shift := by
      nlinarith
    unfold GridSegment.Between at between
    rcases between with between | between <;> omega

/-- If two halo-bounded closed segment occurrences share a point, their
relative translation belongs to the doubled neighboring block. -/
theorem
    PeriodicGridDrawing.relativeTranslate_isDoubleNeighbor_of_contains
    {drawing : PeriodicGridDrawing}
    (endpointBounds : drawing.SegmentEndpointsInExpandedSquare)
    {first second : IndexedGridSegment}
    (firstMember : first ∈ drawing.indexedSegments)
    (secondMember : second ∈ drawing.indexedSegments)
    {firstTranslate secondTranslate point : Cell}
    (firstContains :
      (first.segment.translate
        (drawing.periodTranslation firstTranslate)).Contains point)
    (secondContains :
      (second.segment.translate
        (drawing.periodTranslation secondTranslate)).Contains point) :
    Cell.sub firstTranslate secondTranslate ∈
      PeriodicGridDrawing.doubleNeighborTranslations := by
  let relative := Cell.sub firstTranslate secondTranslate
  let normalized := drawing.normalizePoint point secondTranslate
  have normalizedFirst :
      (first.segment.translate
        (drawing.periodTranslation relative)).Contains normalized :=
    (PeriodicGridDrawing.contains_normalize drawing first.segment
      firstTranslate secondTranslate point).mp firstContains
  have normalizedSecond : second.segment.Contains normalized := by
    simpa [Cell.sub, PeriodicGridDrawing.periodTranslation, Cell.scale,
      GridSegment.translate, Cell.add] using
      (PeriodicGridDrawing.contains_normalize drawing second.segment
        secondTranslate secondTranslate point).mp secondContains
  have normalizedBounds :
      drawing.PositionInExpandedSquare normalized :=
    PeriodicGridDrawing.expanded_of_contains
      (endpointBounds second secondMember).1
      (endpointBounds second secondMember).2
      normalizedSecond
  have periodPositive : (0 : Int) < drawing.gridSize := by
    exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have firstBounds := endpointBounds first firstMember
  apply
    (PeriodicGridDrawing.mem_doubleNeighborTranslations_iff
      relative).mpr
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
      simpa [GridSegment.translate,
        PeriodicGridDrawing.periodTranslation,
        Cell.add, Cell.scale, add_comm] using same
    have between' :
        GridSegment.Between
          (first.segment.start.1 +
            drawing.gridSize * relative.1)
          (first.segment.finish.1 +
            drawing.gridSize * relative.1)
          normalized.1 := by
      simpa [GridSegment.translate,
        PeriodicGridDrawing.periodTranslation,
        Cell.add, Cell.scale, add_comm] using between
    exact
      ⟨between_closed_shift_is_doubleNeighbor periodPositive
          startXLower startXUpper finishXLower finishXUpper
          pointXLower pointXUpper between',
        PeriodicGridDrawing.lane_shift_is_doubleNeighbor
          periodPositive startYLower startYUpper
          pointYLower pointYUpper same'⟩
  · have same' :
        normalized.1 =
          first.segment.start.1 +
            drawing.gridSize * relative.1 := by
      simpa [GridSegment.translate,
        PeriodicGridDrawing.periodTranslation,
        Cell.add, Cell.scale, add_comm] using same
    have between' :
        GridSegment.Between
          (first.segment.start.2 +
            drawing.gridSize * relative.2)
          (first.segment.finish.2 +
            drawing.gridSize * relative.2)
          normalized.2 := by
      simpa [GridSegment.translate,
        PeriodicGridDrawing.periodTranslation,
        Cell.add, Cell.scale, add_comm] using between
    exact
      ⟨PeriodicGridDrawing.lane_shift_is_doubleNeighbor
          periodPositive startXLower startXUpper
          pointXLower pointXUpper same',
        between_closed_shift_is_doubleNeighbor periodPositive
          startYLower startYUpper finishYLower finishYUpper
          pointYLower pointYUpper between'⟩

/-- A segment terminal's named drawing point lies on its segment occurrence,
without requiring the occurrence itself to be one of the finite retained
translations. -/
theorem SegmentTerminal.segment_contains_drawingPoint_of_axisAligned
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (terminal : SegmentTerminal)
    (axisAligned : terminal.indexed.segment.IsAxisAligned) :
    (terminal.indexed.segment.translate
        ((drawing graph).periodTranslation terminal.translate)).Contains
      (terminal.drawingPoint graph) := by
  have translatedAligned :
      (terminal.indexed.segment.translate
        ((drawing graph).periodTranslation
          terminal.translate)).IsAxisAligned :=
    (GridSegment.isAxisAligned_translate _ _).mpr axisAligned
  generalize endpointEq : terminal.endpoint = endpoint
  cases endpoint with
  | start =>
      simpa [SegmentTerminal.drawingPoint, endpointEq] using
        GridSegment.contains_start_of_axisAligned translatedAligned
  | finish =>
      simpa [SegmentTerminal.drawingPoint, endpointEq] using
        GridSegment.contains_finish_of_axisAligned translatedAligned

/-- A lifted constructed-drawing vertex that still lies in the open
one-cell halo must use one of the nine neighboring lattice translations. -/
theorem liftedDrawingVertexPosition_translate_neighbor_of_inExpanded
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {vertex : Vertex}
    (vertexMember : vertex ∈ graph.vertices)
    (translate : Cell)
    (inside :
      InExpandedDrawingSquare graph
        (Cell.add
          ((drawing graph).vertexPosition graph vertex)
          ((drawing graph).periodTranslation translate))) :
    IsNeighborTranslation translate := by
  let period : Int := drawingGridSize graph
  let base := (drawing graph).vertexPosition graph vertex
  let lifted :=
    Cell.add base ((drawing graph).periodTranslation translate)
  have periodPositive : 0 < period := by
    dsimp only [period]
    exact_mod_cast drawingGridSize_pos graph
  have baseBounds :=
    drawing_vertexPosition_in_fundamental_square graph vertexMember
  change
    0 < base.1 ∧ base.1 < period ∧
      0 < base.2 ∧ base.2 < period at baseBounds
  change
    -period < lifted.1 ∧ lifted.1 < 2 * period ∧
      -period < lifted.2 ∧ lifted.2 < 2 * period at inside
  have horizontalEq :
      base.1 = lifted.1 + period * (-translate.1) := by
    simp [base, lifted, period,
      PeriodicGridDrawing.periodTranslation,
      Cell.add, Cell.scale]
  have verticalEq :
      base.2 = lifted.2 + period * (-translate.2) := by
    simp [base, lifted, period,
      PeriodicGridDrawing.periodTranslation,
      Cell.add, Cell.scale]
  have horizontalNegativeNeighbor :=
    lane_shift_is_neighbor
      periodPositive inside.1 inside.2.1
      (le_of_lt baseBounds.1) baseBounds.2.1 horizontalEq
  have verticalNegativeNeighbor :=
    lane_shift_is_neighbor
      periodPositive inside.2.2.1 inside.2.2.2
      (le_of_lt baseBounds.2.2.1) baseBounds.2.2.2 verticalEq
  constructor <;> omega

/-- If a point of the macrocell around a lifted vertex lies in the refined
open one-cell halo, then the vertex occurrence itself is neighboring.  The
unused seven-cell macrocell margin makes the implication strict at both
period boundaries. -/
theorem liftedDrawingVertexPosition_translate_neighbor_of_macrocellPoint_inExpanded
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {vertex : Vertex}
    (vertexMember : vertex ∈ graph.vertices)
    (translate : Cell)
    (point : Cell)
    (pointInMacrocell :
      InPlanarSATMacrocell
        (Cell.add
          ((drawing graph).vertexPosition graph vertex)
          ((drawing graph).periodTranslation translate))
        point)
    (pointInExpandedRefinement :
      let period : Int :=
        planarMacroScale * drawingGridSize graph;
      -period < point.1 ∧ point.1 < 2 * period ∧
        -period < point.2 ∧ point.2 < 2 * period) :
    IsNeighborTranslation translate := by
  let center :=
    Cell.add
      ((drawing graph).vertexPosition graph vertex)
      ((drawing graph).periodTranslation translate)
  let period : Int := drawingGridSize graph
  have periodPositive : 0 < period := by
    dsimp only [period]
    exact_mod_cast drawingGridSize_pos graph
  have centerBounds :
      -period ≤ center.1 ∧ center.1 < 2 * period ∧
        -period ≤ center.2 ∧ center.2 < 2 * period := by
    change
      InClosedGridRectangle
        (planarSATMacrocellRouteLower center)
        (planarSATMacrocellRouteUpper center) point at pointInMacrocell
    simp only [InClosedGridRectangle,
      planarSATMacrocellRouteLower,
      planarSATMacrocellRouteUpper,
      planarMacroScale, Cell.add, Cell.scale] at pointInMacrocell pointInExpandedRefinement
    omega
  have baseBounds :=
    drawing_vertexPosition_in_fundamental_square graph vertexMember
  have horizontalEq :
      center.1 =
        ((drawing graph).vertexPosition graph vertex).1 +
          period * translate.1 := by
    simp [center, period,
      PeriodicGridDrawing.periodTranslation,
      Cell.add, Cell.scale]
  have verticalEq :
      center.2 =
        ((drawing graph).vertexPosition graph vertex).2 +
          period * translate.2 := by
    simp [center, period,
      PeriodicGridDrawing.periodTranslation,
      Cell.add, Cell.scale]
  constructor
  · exact fundamental_translate_shift_is_neighbor
      periodPositive baseBounds.1 baseBounds.2.1
      centerBounds.1 centerBounds.2.1 horizontalEq
  · exact fundamental_translate_shift_is_neighbor
      periodPositive baseBounds.2.2.1 baseBounds.2.2.2
      centerBounds.2.2.1 centerBounds.2.2.2 verticalEq

/-- A segment in the refined expanded square cannot meet a segment in the
macrocell of a non-neighboring lifted vertex.  This continuous formulation
avoids choosing an integer intersection point: separated closed endpoint
boxes directly contradict `InteriorsMeet`. -/
theorem liftedDrawingVertexPosition_translate_neighbor_of_macrocellSegment_meets_expanded
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {vertex : Vertex}
    (vertexMember : vertex ∈ graph.vertices)
    (translate : Cell)
    (expandedSegment macrocellSegment : GridSegment)
    (expandedStart :
      let period : Int :=
        planarMacroScale * drawingGridSize graph;
      -period < expandedSegment.start.1 ∧
        expandedSegment.start.1 < 2 * period ∧
        -period < expandedSegment.start.2 ∧
        expandedSegment.start.2 < 2 * period)
    (expandedFinish :
      let period : Int :=
        planarMacroScale * drawingGridSize graph;
      -period < expandedSegment.finish.1 ∧
        expandedSegment.finish.1 < 2 * period ∧
        -period < expandedSegment.finish.2 ∧
        expandedSegment.finish.2 < 2 * period)
    (macrocellStart :
      InPlanarSATMacrocell
        (Cell.add
          ((drawing graph).vertexPosition graph vertex)
          ((drawing graph).periodTranslation translate))
        macrocellSegment.start)
    (macrocellFinish :
      InPlanarSATMacrocell
        (Cell.add
          ((drawing graph).vertexPosition graph vertex)
          ((drawing graph).periodTranslation translate))
        macrocellSegment.finish)
    (meet :
      GridSegment.InteriorsMeet expandedSegment macrocellSegment) :
    IsNeighborTranslation translate := by
  let period : Int := drawingGridSize graph
  let refinedPeriod : Int := planarMacroScale * period
  let center :=
    Cell.add
      ((drawing graph).vertexPosition graph vertex)
      ((drawing graph).periodTranslation translate)
  let expandedLower : Cell :=
    (-refinedPeriod + 1, -refinedPeriod + 1)
  let expandedUpper : Cell :=
    (2 * refinedPeriod - 1, 2 * refinedPeriod - 1)
  have periodPositive : 0 < period := by
    dsimp only [period]
    exact_mod_cast drawingGridSize_pos graph
  have baseBounds :=
    drawing_vertexPosition_in_fundamental_square graph vertexMember
  change
    0 < ((drawing graph).vertexPosition graph vertex).1 ∧
      ((drawing graph).vertexPosition graph vertex).1 < period ∧
      0 < ((drawing graph).vertexPosition graph vertex).2 ∧
      ((drawing graph).vertexPosition graph vertex).2 < period at baseBounds
  have centerHorizontal :
      center.1 =
        ((drawing graph).vertexPosition graph vertex).1 +
          period * translate.1 := by
    simp [center, period,
      PeriodicGridDrawing.periodTranslation,
      Cell.add, Cell.scale]
  have centerVertical :
      center.2 =
        ((drawing graph).vertexPosition graph vertex).2 +
          period * translate.2 := by
    simp [center, period,
      PeriodicGridDrawing.periodTranslation,
      Cell.add, Cell.scale]
  by_contra notNeighbor
  have translateOutside :
      translate.1 ≤ -2 ∨ 2 ≤ translate.1 ∨
        translate.2 ≤ -2 ∨ 2 ≤ translate.2 := by
    rcases translate with ⟨horizontal, vertical⟩
    simp only [IsNeighborTranslation] at notNeighbor
    omega
  have rectanglesSeparated :
      ClosedGridRectanglesSeparated
        expandedLower expandedUpper
        (planarSATMacrocellRouteLower center)
        (planarSATMacrocellRouteUpper center) := by
    rcases translateOutside with
        horizontalLow | horizontalHigh | verticalLow | verticalHigh
    · have nonnegative :
          0 ≤ period * (-translate.1 - 2) :=
        mul_nonneg (le_of_lt periodPositive) (by omega)
      have productUpper :
          period * translate.1 ≤ -2 * period := by
        nlinarith
      have centerUpper : center.1 ≤ -period - 1 := by
        rw [centerHorizontal]
        have baseUpperInt :
            ((drawing graph).vertexPosition graph vertex).1 ≤
              period - 1 := by
          omega
        omega
      apply Or.inr
      apply Or.inl
      simp only [expandedLower,
        planarSATMacrocellRouteUpper,
        refinedPeriod, planarMacroScale,
        Cell.add, Cell.scale]
      omega
    · have nonnegative :
          0 ≤ period * (translate.1 - 2) :=
        mul_nonneg (le_of_lt periodPositive) (by omega)
      have productLower :
          2 * period ≤ period * translate.1 := by
        nlinarith
      have centerLower : 2 * period + 1 ≤ center.1 := by
        rw [centerHorizontal]
        omega
      apply Or.inl
      simp only [expandedUpper,
        planarSATMacrocellRouteLower,
        refinedPeriod, planarMacroScale,
        Cell.scale]
      omega
    · have nonnegative :
          0 ≤ period * (-translate.2 - 2) :=
        mul_nonneg (le_of_lt periodPositive) (by omega)
      have productUpper :
          period * translate.2 ≤ -2 * period := by
        nlinarith
      have centerUpper : center.2 ≤ -period - 1 := by
        rw [centerVertical]
        have baseUpperInt :
            ((drawing graph).vertexPosition graph vertex).2 ≤
              period - 1 := by
          omega
        omega
      apply Or.inr
      apply Or.inr
      apply Or.inr
      simp only [expandedLower,
        planarSATMacrocellRouteUpper,
        refinedPeriod, planarMacroScale,
        Cell.add, Cell.scale]
      omega
    · have nonnegative :
          0 ≤ period * (translate.2 - 2) :=
        mul_nonneg (le_of_lt periodPositive) (by omega)
      have productLower :
          2 * period ≤ period * translate.2 := by
        nlinarith
      have centerLower : 2 * period + 1 ≤ center.2 := by
        rw [centerVertical]
        omega
      apply Or.inr
      apply Or.inr
      apply Or.inl
      simp only [expandedUpper,
        planarSATMacrocellRouteLower,
        refinedPeriod, planarMacroScale,
        Cell.scale]
      omega
  have expandedStartBounded :
      InClosedGridRectangle
        expandedLower expandedUpper expandedSegment.start := by
    simp only [InClosedGridRectangle, expandedLower,
      expandedUpper, refinedPeriod, period] at expandedStart ⊢
    omega
  have expandedFinishBounded :
      InClosedGridRectangle
        expandedLower expandedUpper expandedSegment.finish := by
    simp only [InClosedGridRectangle, expandedLower,
      expandedUpper, refinedPeriod, period] at expandedFinish ⊢
    omega
  exact
    (not_interiorsMeet_of_inClosedGridRectangles_of_separated
      expandedStartBounded expandedFinishBounded
      macrocellStart macrocellFinish rectanglesSeparated)
      meet

/-- Translation by a fixed cell is injective on grid segments. -/
theorem GridSegment.translate_injective (offset : Cell) :
    Function.Injective (fun segment : GridSegment =>
      segment.translate offset) := by
  intro first second translatedEq
  rcases first with
    ⟨⟨firstStartX, firstStartY⟩,
      ⟨firstFinishX, firstFinishY⟩⟩
  rcases second with
    ⟨⟨secondStartX, secondStartY⟩,
      ⟨secondFinishX, secondFinishY⟩⟩
  rcases offset with ⟨offsetX, offsetY⟩
  simp only [GridSegment.translate, Cell.add,
    GridSegment.mk.injEq, Prod.mk.injEq] at translatedEq ⊢
  omega

/-- The final indexed carrier segment is already the finite physical
segment with its source clause anchor removed.  This is the source
normalization whose endpoints retain the final expanded-square bound. -/
theorem
    FinalGaugedSegmentOccurrenceWitness.indexedSegment_eq_anchorNormalizedPhysical
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedGridSegment}
    {shift : Cell}
    (witness :
      FinalGaugedSegmentOccurrenceWitness formula indexed shift) :
    indexed.segment =
      witness.physicalSegment.translate
        (carrierMacroPeriodTranslation formula.incidenceGraph
          (Cell.neg witness.sourceClauseAnchor)) := by
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula
  have sourceShiftEq :
      Cell.sub witness.physicalShift shift =
        Cell.neg witness.sourceClauseAnchor := by
    rcases shift with ⟨shiftX, shiftY⟩
    simp [FinalGaugedSegmentOccurrenceWitness.physicalShift_eq,
      Cell.sub, Cell.neg]
  have normalizedThenShift :=
    segment_translate_placement_sub_add
      placement witness.physicalSegment witness.physicalShift shift
  rw [sourceShiftEq] at normalizedThenShift
  have normalizedEq :
      indexed.segment =
        witness.physicalSegment.translate
          (placement.translation
            (Cell.neg witness.sourceClauseAnchor)) := by
    apply GridSegment.translate_injective
      (placement.translation shift)
    change
      indexed.segment.translate (placement.translation shift) =
        (witness.physicalSegment.translate
          (placement.translation
            (Cell.neg witness.sourceClauseAnchor))).translate
              (placement.translation shift)
    rw [normalizedThenShift]
    exact witness.segmentEq
  have offsetEq :
      placement.translation
          (Cell.neg witness.sourceClauseAnchor) =
        carrierMacroPeriodTranslation formula.incidenceGraph
          (Cell.neg witness.sourceClauseAnchor) :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro
      formula (Cell.neg witness.sourceClauseAnchor)
  simpa only [offsetEq] using normalizedEq

/-- An anchor-normalized final carrier segment remains inside the explicit
rectangle of the correspondingly translated raw carrier link. -/
theorem
    FinalGaugedSegmentOccurrenceWitness.indexedSegment_endpoints_in_anchorNormalizedCarrierRectangle
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {indexed : IndexedGridSegment}
    {shift : Cell}
    (witness :
      FinalGaugedSegmentOccurrenceWitness formula indexed shift)
    (link : EqualityLink CarrierNode)
    (componentEq :
      witness.routeWitness.metadata.source.component = .carrier link) :
    let anchorShift := Cell.neg witness.sourceClauseAnchor
    let translatedLink :=
      carrierLinkPeriodTranslate formula.incidenceGraph link anchorShift
    InClosedGridRectangle
        (drawingCompleteCarrierLinkRectangleLower
          formula.incidenceGraph translatedLink)
        (drawingCompleteCarrierLinkRectangleUpper
          formula.incidenceGraph translatedLink)
        indexed.segment.start ∧
      InClosedGridRectangle
        (drawingCompleteCarrierLinkRectangleLower
          formula.incidenceGraph translatedLink)
        (drawingCompleteCarrierLinkRectangleUpper
          formula.incidenceGraph translatedLink)
        indexed.segment.finish := by
  rcases
      witness.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq link componentEq with
    ⟨localClauseIndex, sourceEq⟩
  have nonempty :
      witness.routeWitness.metadata.clause.literals ≠ [] := by
    intro empty
    have literalMember := witness.routeWitness.literalMember
    rw [empty] at literalMember
    simp at literalMember
  let anchorShift := Cell.neg witness.sourceClauseAnchor
  let translatedLink :=
    carrierLinkPeriodTranslate formula.incidenceGraph link anchorShift
  have translatedLinkMember :
      translatedLink ∈
        retainedDrawingCompleteCarrierLinksRaw
          formula.incidenceGraph := by
    simpa only [translatedLink, anchorShift,
      FinalGaugedSegmentOccurrenceWitness.sourceClauseAnchor] using
      (witness.routeWitness.metadata
        |>.carrier_anchorNormalize_mem_raw
          wellFormed degree isLocal witness.metadata_retainedValid
          nonempty link localClauseIndex sourceEq)
  have sourceLocalClauseMember :
      (witness.routeWitness.metadata.clause,
          witness.routeWitness.metadata.source.localClauseIndex) ∈
        (witness.routeWitness.metadata.source.clauseFormula
          formula).zipIdx :=
    (witness.routeWitness.metadata
      |>.retainedValid_iff_sourceMember_and_localClauseMember
        formula).mp witness.metadata_retainedValid |>.2
  rcases
      witness.routeWitness.metadata.source
        |>.exists_periodTranslatedClauseLiteral
          formula anchorShift
          witness.routeWitness.metadata.clause
          sourceLocalClauseMember
          witness.routeWitness.literal witness.taggedLiteral.2
          witness.routeWitness.literalMember with
    ⟨translatedClause, translatedLiteral,
      translatedClauseMember, translatedLiteralMember⟩
  have translatedSourceEq :
      witness.routeWitness.metadata.source.periodTranslate
          formula anchorShift =
        .carrier translatedLink localClauseIndex := by
    rw [sourceEq]
    rfl
  have sourceLocalClauseIndexEq :
      witness.routeWitness.metadata.source.localClauseIndex =
        localClauseIndex := by
    rw [sourceEq]
    rfl
  have translatedFormulaClauseMember :
      (translatedClause, localClauseIndex) ∈
        (drawingPlanarSATCarrierFormulaAt
          (Variable := Variable) translatedLink).zipIdx := by
    rw [translatedSourceEq] at translatedClauseMember
    simpa [DrawingPlanarSATClauseSource.localClauseIndex,
      DrawingPlanarSATClauseSource.clauseFormula] using
        translatedClauseMember
  have translatedDrawingClauseMember :
      (translatedClause, localClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula translatedLink).formula.zipIdx := by
    rw [
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula_of_raw
        wellFormed degree isLocal translatedLinkMember]
    exact translatedFormulaClauseMember
  have translatedSegmentMember :=
    witness.physicalSegment_periodTranslate_mem_sourceRoute
      anchorShift
  rw [translatedSourceEq, sourceLocalClauseIndexEq] at translatedSegmentMember
  have translatedEndpoints :=
    gridPolylineSegments_endpoints_mem
      (List.fst_mem_of_mem_zipIdx translatedSegmentMember)
  have bounded :=
    retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_bounded_of_raw
      wellFormed degree isLocal translatedLinkMember
  have startBounded :=
    bounded.of_members translatedDrawingClauseMember
      translatedLiteralMember translatedEndpoints.1
  have finishBounded :=
    bounded.of_members translatedDrawingClauseMember
      translatedLiteralMember translatedEndpoints.2
  have indexedEq :=
    witness.indexedSegment_eq_anchorNormalizedPhysical
  simpa only [anchorShift, translatedLink, indexedEq] using
    And.intro startBounded finishBounded

/-- Undo the two quotient gauges in a final contact, then cancel the carrier's
common physical translate.  The result is a contact between the carrier's
original finite segment and the noncarrier segment translated by exactly the
source shift used by the halo-closure reduction below. -/
theorem
    FinalGaugedSegmentOccurrenceWitness.alignedPhysicalSegments_interiorsMeet_of_final
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (meet :
      GridSegment.InteriorsMeet
        (firstIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift))
        (secondIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift))) :
    GridSegment.InteriorsMeet
      first.physicalSegment
      (second.physicalSegment.translate
        (carrierMacroPeriodTranslation formula.incidenceGraph
          (Cell.sub second.physicalShift first.physicalShift))) := by
  let firstRepresentative :=
    first.toCommonShiftRepresentative
  let secondRepresentative :=
    second.toCommonShiftRepresentative
  rw [firstRepresentative.segmentEq,
    secondRepresentative.segmentEq] at meet
  change
    GridSegment.InteriorsMeet
      (first.physicalSegment.translate
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).translation first.physicalShift))
      (second.physicalSegment.translate
        ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).translation second.physicalShift)) at meet
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula
  let sourceShift :=
    Cell.sub second.physicalShift first.physicalShift
  have secondAlignedEq :
      (second.physicalSegment.translate
        (placement.translation sourceShift)).translate
          (placement.translation first.physicalShift) =
        second.physicalSegment.translate
          (placement.translation second.physicalShift) := by
    exact segment_translate_placement_sub_add
      placement second.physicalSegment
      second.physicalShift first.physicalShift
  rw [← secondAlignedEq] at meet
  have aligned :
      GridSegment.InteriorsMeet
        first.physicalSegment
        (second.physicalSegment.translate
          (placement.translation sourceShift)) :=
    (GridSegment.interiorsMeet_translate_both_iff
      first.physicalSegment
      (second.physicalSegment.translate
        (placement.translation sourceShift))
      (placement.translation first.physicalShift)).mp meet
  have offsetEq :
      placement.translation sourceShift =
        carrierMacroPeriodTranslation
          formula.incidenceGraph sourceShift :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro
      formula sourceShift
  simpa only [sourceShift, offsetEq] using aligned

/-- Cancel the carrier's final lattice translate while keeping its indexed
segment anchor-normalized.  The other physical source is then shifted by its
physical shift minus the carrier's final shift. -/
theorem
    FinalGaugedSegmentOccurrenceWitness.anchorAlignedPhysical_interiorsMeet_of_final
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (meet :
      GridSegment.InteriorsMeet
        (firstIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift))
        (secondIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift))) :
    GridSegment.InteriorsMeet
      firstIndexed.segment
      (second.physicalSegment.translate
        (carrierMacroPeriodTranslation formula.incidenceGraph
          (Cell.sub second.physicalShift firstShift))) := by
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula
  let relativePhysicalShift :=
    Cell.sub second.physicalShift first.physicalShift
  let anchorShift := Cell.neg first.sourceClauseAnchor
  let targetShift := Cell.sub second.physicalShift firstShift
  have alignedPhysical :
      GridSegment.InteriorsMeet
        first.physicalSegment
        (second.physicalSegment.translate
          (placement.translation relativePhysicalShift)) := by
    have aligned :=
      first.alignedPhysicalSegments_interiorsMeet_of_final second meet
    have offsetEq :
        placement.translation relativePhysicalShift =
          carrierMacroPeriodTranslation formula.incidenceGraph
            relativePhysicalShift :=
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro
        formula relativePhysicalShift
    simpa only [relativePhysicalShift, offsetEq] using aligned
  have shiftedMeet :
      GridSegment.InteriorsMeet
        (first.physicalSegment.translate
          (placement.translation anchorShift))
        ((second.physicalSegment.translate
          (placement.translation relativePhysicalShift)).translate
            (placement.translation anchorShift)) :=
    (GridSegment.interiorsMeet_translate_both_iff
      first.physicalSegment
      (second.physicalSegment.translate
        (placement.translation relativePhysicalShift))
      (placement.translation anchorShift)).mpr alignedPhysical
  have relativeShiftEq :
      Cell.sub targetShift anchorShift = relativePhysicalShift := by
    rcases firstShift with ⟨firstX, firstY⟩
    rcases second.physicalShift with ⟨secondX, secondY⟩
    rcases first.sourceClauseAnchor with ⟨anchorX, anchorY⟩
    simp only [targetShift, anchorShift, relativePhysicalShift,
      FinalGaugedSegmentOccurrenceWitness.physicalShift_eq,
      Cell.sub, Cell.neg, Prod.mk.injEq]
    constructor <;> ring
  have secondShiftedEq :
      (second.physicalSegment.translate
        (placement.translation relativePhysicalShift)).translate
          (placement.translation anchorShift) =
        second.physicalSegment.translate
          (placement.translation targetShift) := by
    have translated :=
      segment_translate_placement_sub_add
        placement second.physicalSegment targetShift anchorShift
    rwa [relativeShiftEq] at translated
  have firstEq :
      first.physicalSegment.translate
          (placement.translation anchorShift) =
        firstIndexed.segment := by
    rw [first.indexedSegment_eq_anchorNormalizedPhysical]
    have offsetEq :
        placement.translation anchorShift =
          carrierMacroPeriodTranslation formula.incidenceGraph
            anchorShift :=
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro
        formula anchorShift
    simp only [anchorShift, offsetEq]
  have targetOffsetEq :
      placement.translation targetShift =
        carrierMacroPeriodTranslation formula.incidenceGraph
          targetShift :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro
      formula targetShift
  simpa only [firstEq, secondShiftedEq, targetShift,
    targetOffsetEq] using shiftedMeet

/-- Translating a noncarrier witness's physical segment translates both
endpoint macrocell certificates by the same drawing-period shift. -/
theorem
    FinalGaugedSegmentOccurrenceWitness.translatedPhysicalSegment_endpoints_in_macrocell
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {indexed : IndexedGridSegment}
    {shift : Cell}
    (witness :
      FinalGaugedSegmentOccurrenceWitness formula indexed shift)
    (notCarrier :
      ¬∃ link,
        witness.routeWitness.metadata.source.component =
          DrawingPlanarSATComponent.carrier link)
    (center : Cell)
    (centerEq :
      witness.routeWitness.metadata.source.component.macrocellCenter
          formula =
        some center)
    (sourceShift : Cell) :
    let translatedSegment :=
      witness.physicalSegment.translate
        (carrierMacroPeriodTranslation formula.incidenceGraph sourceShift)
    InPlanarSATMacrocell
        (Cell.add center
          ((drawing formula.incidenceGraph).periodTranslation sourceShift))
        translatedSegment.start ∧
      InPlanarSATMacrocell
        (Cell.add center
          ((drawing formula.incidenceGraph).periodTranslation sourceShift))
        translatedSegment.finish := by
  have valid :=
    witness.routeWitness.metadata
      |>.valid_of_retainedValid_of_not_carrier
        witness.metadata_retainedValid notCarrier
  have endpointMembers :=
    gridPolylineSegments_endpoints_mem
      (List.fst_mem_of_mem_zipIdx
        witness.physicalSegment_mem_sourceRoute)
  have startBounded :=
    witness.routeWitness.metadata.localRoutePoints_inPlanarSATMacrocell
      wellFormed degree isLocal valid center centerEq
      witness.routeWitness.literalMember endpointMembers.1
  have finishBounded :=
    witness.routeWitness.metadata.localRoutePoints_inPlanarSATMacrocell
      wellFormed degree isLocal valid center centerEq
      witness.routeWitness.literalMember endpointMembers.2
  have translatedStart :=
    inPlanarSATMacrocell_translate
      (shift := sourceShift)
      (drawingGridSize formula.incidenceGraph) startBounded
  have translatedFinish :=
    inPlanarSATMacrocell_translate
      (shift := sourceShift)
      (drawingGridSize formula.incidenceGraph) finishBounded
  constructor
  · simpa [GridSegment.translate,
      carrierMacroPeriodTranslation,
      PeriodicGridDrawing.periodTranslation,
      Cell.add, Cell.scale, planarMacroScale,
      add_comm, mul_assoc, mul_comm, mul_left_comm] using translatedStart
  · simpa [GridSegment.translate,
      carrierMacroPeriodTranslation,
      PeriodicGridDrawing.periodTranslation,
      Cell.add, Cell.scale, planarMacroScale,
      add_comm, mul_assoc, mul_comm, mul_left_comm] using translatedFinish

/-- If an anchor-normalized carrier segment meets a translated noncarrier
component, its supporting segment passes through the translated center of
that component's macrocell. -/
theorem
    FinalGaugedSegmentOccurrenceWitness.anchorNormalizedCarrier_supportingSegment_contains_translatedMacrocellCenter_of_contact
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (link : EqualityLink CarrierNode)
    (firstComponentEq :
      first.routeWitness.metadata.source.component = .carrier link)
    (secondNotCarrier :
      ¬∃ secondLink,
        second.routeWitness.metadata.source.component =
          .carrier secondLink)
    (center : Cell)
    (centerEq :
      second.routeWitness.metadata.source.component.macrocellCenter
          formula =
        some center)
    (meet :
      GridSegment.InteriorsMeet
        (firstIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift))
        (secondIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift))) :
    let graph := formula.incidenceGraph
    let anchorShift := Cell.neg first.sourceClauseAnchor
    let sourceShift := Cell.sub second.physicalShift firstShift
    let translatedLink :=
      carrierLinkPeriodTranslate graph link anchorShift
    (translatedLink.first.supportingSegment graph).Contains
      (Cell.add center
        ((drawing graph).periodTranslation sourceShift)) := by
  let graph := formula.incidenceGraph
  let anchorShift := Cell.neg first.sourceClauseAnchor
  let sourceShift := Cell.sub second.physicalShift firstShift
  let translatedLink :=
    carrierLinkPeriodTranslate graph link anchorShift
  rcases
      first.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq
          link firstComponentEq with
    ⟨localClauseIndex, firstSourceEq⟩
  have firstNonempty :
      first.routeWitness.metadata.clause.literals ≠ [] := by
    intro empty
    have literalMember := first.routeWitness.literalMember
    rw [empty] at literalMember
    simp at literalMember
  have translatedLinkMember :
      translatedLink ∈
        retainedDrawingCompleteCarrierLinksRaw graph := by
    simpa only [translatedLink, graph, anchorShift,
      FinalGaugedSegmentOccurrenceWitness.sourceClauseAnchor] using
      (first.routeWitness.metadata
        |>.carrier_anchorNormalize_mem_raw
          wellFormed degree isLocal first.metadata_retainedValid
          firstNonempty link localClauseIndex firstSourceEq)
  have firstBounds :=
    first.indexedSegment_endpoints_in_anchorNormalizedCarrierRectangle
      wellFormed degree isLocal link firstComponentEq
  have secondBounds :=
    second.translatedPhysicalSegment_endpoints_in_macrocell
      wellFormed degree isLocal secondNotCarrier
      center centerEq sourceShift
  have aligned :=
    first.anchorAlignedPhysical_interiorsMeet_of_final second meet
  have notSeparated :
      ¬ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower
          graph translatedLink)
        (drawingCompleteCarrierLinkRectangleUpper
          graph translatedLink)
        (planarSATMacrocellRouteLower
          (Cell.add center
            ((drawing graph).periodTranslation sourceShift)))
        (planarSATMacrocellRouteUpper
          (Cell.add center
            ((drawing graph).periodTranslation sourceShift))) := by
    intro separated
    exact
      (not_interiorsMeet_of_inClosedGridRectangles_of_separated
        firstBounds.1 firstBounds.2
        secondBounds.1 secondBounds.2 separated)
        aligned
  exact
    retainedDrawingCompleteCarrierLinkRaw_supportingSegment_contains_of_macrocell_overlap
      wellFormed degree isLocal translatedLinkMember
      (Cell.add center
        ((drawing graph).periodTranslation sourceShift))
      notSeparated

/-- If an anchor-normalized carrier segment meets a translated component
inside the macrocell of a lifted incidence-graph vertex, the carrier's first
source occurrence and that lifted vertex occurrence differ by a neighboring
lattice translation. -/
theorem
    FinalGaugedSegmentOccurrenceWitness.carrier_liftedVertex_relative_neighbor_of_contact
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (link : EqualityLink CarrierNode)
    (firstComponentEq :
      first.routeWitness.metadata.source.component = .carrier link)
    (secondNotCarrier :
      ¬∃ secondLink,
        second.routeWitness.metadata.source.component =
          .carrier secondLink)
    (vertex : CNFVertex Variable)
    (vertexMember : vertex ∈ formula.incidenceGraph.vertices)
    (vertexTranslate : Cell)
    (centerEq :
      second.routeWitness.metadata.source.component.macrocellCenter
          formula =
        some
          (liftedIncidenceVertexPosition
            formula vertex vertexTranslate))
    (meet :
      GridSegment.InteriorsMeet
        (firstIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift))
        (secondIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift))) :
    IsNeighborTranslation
      (Cell.sub
        (Cell.add link.first.translate
          (Cell.neg first.sourceClauseAnchor))
        (Cell.add vertexTranslate
          (Cell.sub second.physicalShift firstShift))) := by
  let graph := formula.incidenceGraph
  let anchorShift := Cell.neg first.sourceClauseAnchor
  let sourceShift := Cell.sub second.physicalShift firstShift
  let targetVertexTranslate :=
    Cell.add vertexTranslate sourceShift
  let translatedLink :=
    carrierLinkPeriodTranslate graph link anchorShift
  rcases
      first.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq
          link firstComponentEq with
    ⟨localClauseIndex, firstSourceEq⟩
  have firstNonempty :
      first.routeWitness.metadata.clause.literals ≠ [] := by
    intro empty
    have literalMember := first.routeWitness.literalMember
    rw [empty] at literalMember
    simp at literalMember
  have translatedLinkMember :
      translatedLink ∈
        retainedDrawingCompleteCarrierLinksRaw graph := by
    simpa only [translatedLink, graph, anchorShift,
      FinalGaugedSegmentOccurrenceWitness.sourceClauseAnchor] using
      (first.routeWitness.metadata
        |>.carrier_anchorNormalize_mem_raw
          wellFormed degree isLocal first.metadata_retainedValid
          firstNonempty link localClauseIndex firstSourceEq)
  have firstBounds :=
    first.indexedSegment_endpoints_in_anchorNormalizedCarrierRectangle
      wellFormed degree isLocal link firstComponentEq
  have secondBounds :=
    second.translatedPhysicalSegment_endpoints_in_macrocell
      wellFormed degree isLocal secondNotCarrier
      (liftedIncidenceVertexPosition
        formula vertex vertexTranslate)
      centerEq sourceShift
  have targetCenterEq :
      Cell.add
          (liftedIncidenceVertexPosition
            formula vertex vertexTranslate)
          ((drawing graph).periodTranslation sourceShift) =
        liftedIncidenceVertexPosition
          formula vertex targetVertexTranslate := by
    exact
      (liftedIncidenceVertexPosition_periodTranslate
        formula vertex vertexTranslate sourceShift).symm
  rw [targetCenterEq] at secondBounds
  have aligned :=
    first.anchorAlignedPhysical_interiorsMeet_of_final second meet
  have notSeparated :
      ¬ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower
          graph translatedLink)
        (drawingCompleteCarrierLinkRectangleUpper
          graph translatedLink)
        (planarSATMacrocellRouteLower
          (liftedIncidenceVertexPosition
            formula vertex targetVertexTranslate))
        (planarSATMacrocellRouteUpper
          (liftedIncidenceVertexPosition
            formula vertex targetVertexTranslate)) := by
    intro separated
    exact
      (not_interiorsMeet_of_inClosedGridRectangles_of_separated
        firstBounds.1 firstBounds.2
        secondBounds.1 secondBounds.2 separated)
        aligned
  have centerContains :
      translatedLink.first.supportingSegment graph |>.Contains
        (liftedIncidenceVertexPosition
          formula vertex targetVertexTranslate) :=
    retainedDrawingCompleteCarrierLinkRaw_supportingSegment_contains_of_macrocell_overlap
      wellFormed degree isLocal translatedLinkMember
      (liftedIncidenceVertexPosition
        formula vertex targetVertexTranslate)
      notSeparated
  let relative :=
    Cell.sub translatedLink.first.translate targetVertexTranslate
  have normalizedContains :
      (translatedLink.first.indexed.segment.translate
          ((drawing graph).periodTranslation relative)).Contains
        ((drawing graph).vertexPosition graph vertex) := by
    have shifted :=
      segment_periodTranslate_sub_contains
        graph translatedLink.first.indexed.segment
        translatedLink.first.translate targetVertexTranslate
        (liftedIncidenceVertexPosition
          formula vertex targetVertexTranslate)
        (by
          simpa [CarrierNode.supportingSegment] using
            centerContains)
    dsimp only [graph] at shifted ⊢
    simpa [relative, liftedIncidenceVertexPosition,
      Cell.sub, PeriodicGridDrawing.periodTranslation,
      Cell.add, Cell.scale] using shifted
  have translatedEndpoints :=
    retainedDrawingCompleteCarrierLinkRaw_endpoints_mem
      graph translatedLinkMember
  have indexedMember :
      translatedLink.first.indexed ∈
        (drawing graph).indexedSegments :=
    retainedCarrierNode_indexed_mem graph translatedEndpoints.1
  have relativeNeighbor :
      IsNeighborTranslation relative :=
    drawing_occurrence_translate_isNeighbor_of_contains
      wellFormed degree isLocal indexedMember
      (by
        have bounds :=
          drawing_vertexPosition_in_fundamental_square
            graph vertexMember
        unfold
          PeriodicGridDrawing.PositionInFundamentalSquare at bounds
        unfold InFundamentalDrawingSquare
        simpa only [graph, drawing_gridSize] using
          And.intro (le_of_lt bounds.1)
            (And.intro bounds.2.1
              (And.intro (le_of_lt bounds.2.2.1)
                bounds.2.2.2)))
      normalizedContains
  simpa [relative, translatedLink, targetVertexTranslate,
    anchorShift, sourceShift, graph,
    CarrierNode.translate_periodTranslate, Cell.sub,
    Cell.add, Cell.neg, add_assoc] using relativeNeighbor

/-- The final gauged drawing has exactly the refined planar-SAT period used
by the macrocell contact bounds. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_gridSize_int
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      formula).gridSize : Int) =
      planarMacroScale * drawingGridSize formula.incidenceGraph := by
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula
  have periodPositive : 0 < placement.period := by
    simpa [placement,
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
      wrappedDrawingPeriodicPlanarSATPlacement] using
      drawingPeriodicPlanarSATPlacement_period_pos formula
  have gridSizeEq :
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
        formula).gridSize =
        placement.period := by
    simpa [
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing]
      using
        PositionedPeriodicCNF.incidenceDrawing_gridSize
          (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
            formula)
          placement
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
            formula)
          periodPositive
  rw [gridSizeEq]
  simp [placement,
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
    wrappedDrawingPeriodicPlanarSATPlacement,
    drawingPeriodicPlanarSATPlacement,
    planarMacroScale]

/-- For any retained noncarrier clause, the source-clause anchor is the
coordinatewise drawing-period quotient of its component's macrocell center.
Thus the gauging translation normalizes the entire component occurrence, not
just the chosen clause position. -/
theorem
    DrawingPlanarSATClauseMetadata.sourceClauseAnchor_eq_macrocellCenter_ediv
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (center : Cell)
    (centerEq :
      metadata.source.component.macrocellCenter formula = some center)
    (nonempty : metadata.clause.literals ≠ []) :
    PeriodicCNF.clauseAnchor
        (metadataGaugedPositionedClause formula metadata).literals =
      (center.1 / drawingGridSize formula.incidenceGraph,
        center.2 / drawingGridSize formula.incidenceGraph) := by
  have clauseBounded :=
    metadata.retainedClausePosition_in_macrocell
      wellFormed degree isLocal valid center centerEq nonempty
  have centerBounded :
      InPlanarSATMacrocell center
        (Cell.scale planarMacroScale center) := by
    rcases center with ⟨centerX, centerY⟩
    norm_num [InPlanarSATMacrocell,
      planarSATMacrocellRouteLower,
      planarSATMacrocellRouteUpper,
      InClosedGridRectangle, Cell.add, Cell.scale,
      planarMacroScale]
  have quotientEq :=
    macrocellQuotient_eq
      (periodFactor := drawingGridSize formula.incidenceGraph)
      clauseBounded centerBounded
  rw [metadata.sourceClauseAnchor_eq_position_ediv
    wellFormed degree isLocal valid nonempty]
  simpa [drawingPeriodicPlanarSATPlacement,
    planarMacroScale, Cell.scale] using quotientEq

/-- Dividing a translated half-open representative by the drawing period
recovers its lattice translation coordinatewise. -/
theorem PeriodicGridDrawing.translatedHalfOpenPosition_ediv
    (drawing : PeriodicGridDrawing)
    {base shift : Cell}
    (baseBounds :
      0 ≤ base.1 ∧ base.1 < drawing.gridSize ∧
        0 ≤ base.2 ∧ base.2 < drawing.gridSize) :
    ((Cell.add base (drawing.periodTranslation shift)).1 /
        drawing.gridSize,
      (Cell.add base (drawing.periodTranslation shift)).2 /
        drawing.gridSize) =
      shift := by
  have periodNe : (drawing.gridSize : Int) ≠ 0 := by
    have periodPositive : 0 < drawing.gridSize :=
      Nat.zero_lt_succ drawing.gridSizePred
    exact_mod_cast periodPositive.ne'
  have horizontalBaseQuotient :
      base.1 / (drawing.gridSize : Int) = 0 :=
    Int.ediv_eq_zero_of_lt baseBounds.1 baseBounds.2.1
  have verticalBaseQuotient :
      base.2 / (drawing.gridSize : Int) = 0 :=
    Int.ediv_eq_zero_of_lt baseBounds.2.2.1 baseBounds.2.2.2
  apply Prod.ext
  · simp only [Cell.add,
      PeriodicGridDrawing.periodTranslation, Cell.scale]
    rw [mul_comm, Int.add_mul_ediv_right _ _ periodNe,
      horizontalBaseQuotient]
    simp
  · simp only [Cell.add,
      PeriodicGridDrawing.periodTranslation, Cell.scale]
    rw [mul_comm, Int.add_mul_ediv_right _ _ periodNe,
      verticalBaseQuotient]
    simp

/-- The coordinatewise period quotient of a lifted incidence-graph vertex
is exactly its occurrence translation. -/
theorem liftedIncidenceVertexPosition_ediv
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {vertex : CNFVertex Variable}
    (vertexMember : vertex ∈ formula.incidenceGraph.vertices)
    (translate : Cell) :
    ((liftedIncidenceVertexPosition formula vertex translate).1 /
        drawingGridSize formula.incidenceGraph,
      (liftedIncidenceVertexPosition formula vertex translate).2 /
        drawingGridSize formula.incidenceGraph) =
      translate := by
  have vertexBounds :=
    drawing_vertexPosition_in_fundamental_square
      formula.incidenceGraph vertexMember
  have halfOpenBounds :
      0 ≤ ((drawing formula.incidenceGraph).vertexPosition
          formula.incidenceGraph vertex).1 ∧
        ((drawing formula.incidenceGraph).vertexPosition
            formula.incidenceGraph vertex).1 <
          (drawing formula.incidenceGraph).gridSize ∧
        0 ≤ ((drawing formula.incidenceGraph).vertexPosition
          formula.incidenceGraph vertex).2 ∧
        ((drawing formula.incidenceGraph).vertexPosition
            formula.incidenceGraph vertex).2 <
          (drawing formula.incidenceGraph).gridSize := by
    simpa [drawing_gridSize] using
      ⟨le_of_lt vertexBounds.1, vertexBounds.2.1,
        le_of_lt vertexBounds.2.2.1, vertexBounds.2.2.2⟩
  simpa [liftedIncidenceVertexPosition, drawing_gridSize] using
    (PeriodicGridDrawing.translatedHalfOpenPosition_ediv
      (drawing formula.incidenceGraph) halfOpenBounds)

/-- If a noncarrier component is centered at a lifted incidence-graph
vertex, its clause anchor is the occurrence translation of that vertex. -/
theorem
    DrawingPlanarSATClauseMetadata.sourceClauseAnchor_eq_liftedVertexTranslate
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (nonempty : metadata.clause.literals ≠ [])
    (vertex : CNFVertex Variable)
    (vertexMember : vertex ∈ formula.incidenceGraph.vertices)
    (translate : Cell)
    (centerEq :
      metadata.source.component.macrocellCenter formula =
        some
          (liftedIncidenceVertexPosition formula vertex translate)) :
    PeriodicCNF.clauseAnchor
        (metadataGaugedPositionedClause formula metadata).literals =
      translate := by
  rw [metadata.sourceClauseAnchor_eq_macrocellCenter_ediv
    wellFormed degree isLocal valid
    (liftedIncidenceVertexPosition formula vertex translate)
    centerEq nonempty]
  exact liftedIncidenceVertexPosition_ediv
    formula vertexMember translate

/-- A local protoedge offset is one of the nine neighboring translations. -/
theorem PeriodicEdge.offset_neighbor_of_local
    {Vertex : Type*}
    (edge : PeriodicEdge Vertex)
    (edgeLocal : edge.span ≤ 1) :
    IsNeighborTranslation edge.offset := by
  rcases offset_eq_of_span_le_one edge edgeLocal with
    offset | offset | offset | offset | offset <;>
    simp [offset, IsNeighborTranslation]

/-- Every semantic bend-center placement of a local protoedge crosses at
most one period boundary. -/
theorem routeBendCenterPlacement_offset_neighbor
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (isLocal : graph.IsLocal)
    {edge : PeriodicEdge Vertex}
    {edgeIndex : Nat}
    (edgeMember : (edge, edgeIndex) ∈ graph.edges.zipIdx)
    {placement : RouteBendCenterPlacement Vertex}
    (placementMember :
      placement ∈ routeBendCenterPlacements graph edge edgeIndex) :
    IsNeighborTranslation placement.offset := by
  have edgeLocal : edge.span ≤ 1 :=
    isLocal edge (List.fst_mem_of_mem_zipIdx edgeMember)
  rcases offset_eq_of_span_le_one edge edgeLocal with
    offset | offset | offset | offset | offset
  all_goals
    simp [routeBendCenterPlacements, offset] at placementMember
  all_goals
    aesop (config := { warnOnNonterminal := false }) <;>
      simp [IsNeighborTranslation]

/-- Gauging a retained bend clause by its source-clause anchor leaves the
route occurrence at the inverse of its semantic boundary offset, hence in
the neighboring route halo. -/
theorem DrawingPlanarSATClauseMetadata.bend_anchorNormalize_translate_neighbor
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (nonempty : metadata.clause.literals ≠ [])
    (routeBend : RouteBend)
    (localClauseIndex : Nat)
    (sourceEq :
      metadata.source = .bend routeBend localClauseIndex) :
    IsNeighborTranslation
      (Cell.add routeBend.translate
        (Cell.neg
          (PeriodicCNF.clauseAnchor
            (metadataGaugedPositionedClause formula metadata).literals))) := by
  let graph := formula.incidenceGraph
  have valid' := valid
  unfold DrawingPlanarSATClauseMetadata.RetainedValid at valid'
  rw [sourceEq] at valid'
  have routeBendMember :
      routeBend ∈ drawingRouteBends graph :=
    List.mem_dedup.mp valid'.1
  rcases drawingRouteBend_centerPlacement
      graph isLocal routeBendMember with
    ⟨edge, edgeIndex, placement, placementIndex,
      edgeMember, placementMember, _routeIndexEq,
      _placementIndexEq, pointEq⟩
  have placementListMember :
      placement ∈ routeBendCenterPlacements graph edge edgeIndex :=
    List.fst_mem_of_mem_zipIdx placementMember
  have placementValid :
      placement.kind.Valid graph :=
    routeBendCenterPlacements_kind_valid
      edgeMember placementListMember
  have placementBounds :=
    RouteBendCenterKind.position_in_fundamental
      wellFormed degree placementValid
  have centerEq :
      metadata.source.component.macrocellCenter formula =
        some (routeBend.drawingPoint graph) := by
    rw [sourceEq]
    rfl
  have anchorEq :=
    metadata.sourceClauseAnchor_eq_macrocellCenter_ediv
      wellFormed degree isLocal valid
      (routeBend.drawingPoint graph) centerEq nonempty
  have pointQuotient :
      ((routeBend.drawingPoint graph).1 / drawingGridSize graph,
        (routeBend.drawingPoint graph).2 / drawingGridSize graph) =
        Cell.add routeBend.translate placement.offset := by
    rw [pointEq]
    simpa [drawing_gridSize] using
      (PeriodicGridDrawing.translatedHalfOpenPosition_ediv
        (drawing graph) placementBounds)
  have normalizedTranslateEq :
      Cell.add routeBend.translate
          (Cell.neg
            (PeriodicCNF.clauseAnchor
              (metadataGaugedPositionedClause formula metadata).literals)) =
        Cell.neg placement.offset := by
    rw [anchorEq, pointQuotient]
    rcases routeBend.translate with ⟨routeX, routeY⟩
    rcases placement.offset with ⟨offsetX, offsetY⟩
    simp [Cell.add, Cell.neg, Cell.sub]
  rw [normalizedTranslateEq]
  exact
    (routeBendCenterPlacement_offset_neighbor
      isLocal edgeMember placementListMember).neg

/-- The anchor-normalized representative of every retained bend source is
itself retained in the finite neighboring bend family. -/
theorem DrawingPlanarSATClauseMetadata.bend_anchorNormalize_retainedComponentMember
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (nonempty : metadata.clause.literals ≠ [])
    (routeBend : RouteBend)
    (localClauseIndex : Nat)
    (sourceEq :
      metadata.source = .bend routeBend localClauseIndex) :
    (metadata.source.periodTranslate formula
      (Cell.neg
        (PeriodicCNF.clauseAnchor
          (metadataGaugedPositionedClause formula metadata).literals))
        |>.RetainedComponentMember formula) := by
  have sourceMember :
      (DrawingPlanarSATClauseSource.bend
        routeBend localClauseIndex).RetainedComponentMember formula := by
    have valid' := valid
    unfold DrawingPlanarSATClauseMetadata.RetainedValid at valid'
    rw [sourceEq] at valid'
    exact valid'.1
  rw [sourceEq]
  exact
    bendSource_periodTranslate_retainedComponentMember_of_neighbor
      formula routeBend localClauseIndex sourceMember
      (Cell.neg
        (PeriodicCNF.clauseAnchor
          (metadataGaugedPositionedClause formula metadata).literals))
      (metadata.bend_anchorNormalize_translate_neighbor
        wellFormed degree isLocal valid nonempty
        routeBend localClauseIndex sourceEq)

/-- A retained crossover clause uses its crossing point as macrocell center,
so its source-clause anchor is exactly the crossing's extracted period
shift. -/
theorem DrawingPlanarSATClauseMetadata.crossover_sourceClauseAnchor_eq_periodShift
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (nonempty : metadata.clause.literals ≠ [])
    (crossing : CrossingRecord)
    (localClauseIndex : Nat)
    (sourceEq :
      metadata.source = .crossover crossing localClauseIndex) :
    PeriodicCNF.clauseAnchor
        (metadataGaugedPositionedClause formula metadata).literals =
      crossingPeriodShift formula.incidenceGraph crossing := by
  have centerEq :
      metadata.source.component.macrocellCenter formula =
        some crossing.point := by
    rw [sourceEq]
    rfl
  simpa [crossingPeriodShift] using
    (metadata.sourceClauseAnchor_eq_macrocellCenter_ediv
      wellFormed degree isLocal valid crossing.point centerEq nonempty)

/-- Anchor-normalizing a retained crossover source is exactly periodic
normalization of its crossing record, which is a canonical oriented
crossing and hence remains in the retained crossing halo. -/
theorem
    DrawingPlanarSATClauseMetadata.crossover_anchorNormalize_retainedComponentMember
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (nonempty : metadata.clause.literals ≠ [])
    (crossing : CrossingRecord)
    (localClauseIndex : Nat)
    (sourceEq :
      metadata.source = .crossover crossing localClauseIndex) :
    (metadata.source.periodTranslate formula
      (Cell.neg
        (PeriodicCNF.clauseAnchor
          (metadataGaugedPositionedClause formula metadata).literals))
        |>.RetainedComponentMember formula) := by
  let graph := formula.incidenceGraph
  have valid' := valid
  unfold DrawingPlanarSATClauseMetadata.RetainedValid at valid'
  rw [sourceEq] at valid'
  have normalizedMember :
      crossing.periodNormalize graph ∈ orientedCrossingHalo graph :=
    orientedCrossings_subset_orientedCrossingHalo graph
      (periodNormalize_mem_orientedCrossings
        wellFormed degree isLocal valid'.1)
  rw [sourceEq,
    metadata.crossover_sourceClauseAnchor_eq_periodShift
      wellFormed degree isLocal valid nonempty
      crossing localClauseIndex sourceEq]
  apply crossoverSource_periodTranslate_retainedComponentMember
  rw [CrossingRecord.periodTranslate_neg_shift_eq_periodNormalize]
  exact normalizedMember

/-- A retained routed-clause source is centered at its lifted clause site,
so anchor normalization moves that site to the zero occurrence and keeps it
in the retained neighboring site family. -/
theorem
    DrawingPlanarSATClauseMetadata.routedClause_anchorNormalize_retainedComponentMember
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (nonempty : metadata.clause.literals ≠ [])
    (site : ClauseRouteSite)
    (sourceEq : metadata.source = .routedClause site) :
    (metadata.source.periodTranslate formula
      (Cell.neg
        (PeriodicCNF.clauseAnchor
          (metadataGaugedPositionedClause formula metadata).literals))
        |>.RetainedComponentMember formula) := by
  have valid' := valid
  unfold DrawingPlanarSATClauseMetadata.RetainedValid at valid'
  rw [sourceEq] at valid'
  have centerEq :
      metadata.source.component.macrocellCenter formula =
        some
          (liftedIncidenceVertexPosition
            formula (.clause site.1) site.2) := by
    rw [sourceEq]
    rfl
  have anchorEq :=
    metadata.sourceClauseAnchor_eq_liftedVertexTranslate
      wellFormed degree isLocal valid nonempty
      (.clause site.1)
      (drawingClauseRouteSite_vertex_mem formula valid'.1)
      site.2 centerEq
  rw [sourceEq, anchorEq]
  apply
    routedClauseSource_periodTranslate_retainedComponentMember_of_neighbor
      formula site valid'.1 (Cell.neg site.2)
  rcases site.2 with ⟨siteX, siteY⟩
  simp [Cell.add, Cell.neg, Cell.sub, IsNeighborTranslation]

/-- Anchor normalization of a retained routed-variable arm leaves its
witnessing route occurrence at the inverse local protoedge offset.  This is
the neighboring orbit condition needed to reindex the arm, even when the
sorted arm index itself changes. -/
theorem
    DrawingPlanarSATClauseMetadata.routedVariable_anchorNormalize_retainedOrbitCondition
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (nonempty : metadata.clause.literals ≠ [])
    (site : VariableRouteSite Variable)
    (armIndex : Nat)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable))
    (localClauseIndex : Nat)
    (sourceEq :
      metadata.source =
        .routedVariable site armIndex arm link localClauseIndex) :
    metadata.source.RetainedOrbitCondition formula
      (Cell.neg
        (PeriodicCNF.clauseAnchor
          (metadataGaugedPositionedClause formula metadata).literals)) := by
  have valid' := valid
  unfold DrawingPlanarSATClauseMetadata.RetainedValid at valid'
  rw [sourceEq] at valid'
  rcases
      exists_routeOccurrence_of_routedVariableLinkMember
        formula site valid'.2.1 with
    ⟨occurrence, occurrenceMember, linkFirstEq⟩
  have occurrenceData :=
    variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
      formula site occurrenceMember
  have centerEq :
      metadata.source.component.macrocellCenter formula =
        some
          (liftedIncidenceVertexPosition
            formula (.variable site.1) site.2) := by
    rw [sourceEq]
    rfl
  have anchorEq :=
    metadata.sourceClauseAnchor_eq_liftedVertexTranslate
      wellFormed degree isLocal valid nonempty
      (.variable site.1)
      (drawingVariableRouteSite_vertex_mem formula valid'.1)
      site.2 centerEq
  rw [sourceEq, anchorEq]
  refine ⟨occurrence, occurrenceMember, linkFirstEq, ?_⟩
  have siteTranslateEq :
      Cell.add occurrence.translate occurrence.edge.offset = site.2 :=
    congrArg Prod.snd occurrenceData.2
  have edgeMember :=
    occurrence.taggedEdge_mem formula occurrenceData.1
  have edgeLocal : occurrence.edge.span ≤ 1 :=
    isLocal occurrence.edge
      (List.fst_mem_of_mem_zipIdx edgeMember)
  have offsetNeighbor :
      IsNeighborTranslation occurrence.edge.offset :=
    PeriodicEdge.offset_neighbor_of_local
      occurrence.edge edgeLocal
  have normalizedTranslateEq :
      Cell.add occurrence.translate (Cell.neg site.2) =
        Cell.neg occurrence.edge.offset := by
    rw [← siteTranslateEq]
    rcases occurrence.translate with ⟨translateX, translateY⟩
    rcases occurrence.edge.offset with ⟨offsetX, offsetY⟩
    simp [Cell.add, Cell.neg, Cell.sub]
  rw [normalizedTranslateEq]
  exact offsetNeighbor.neg

/-- Every retained noncarrier source satisfies its family-specific orbit
condition after subtracting its source-clause anchor.  Exact translated
membership handles crossovers, bends, and routed clauses; routed-variable
arms use the occurrence witness above because their sorted arm index may
change. -/
theorem
    DrawingPlanarSATClauseMetadata.noncarrier_anchorNormalize_retainedOrbitCondition
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (nonempty : metadata.clause.literals ≠ [])
    (notCarrier :
      ¬∃ link,
        metadata.source.component =
          DrawingPlanarSATComponent.carrier link) :
    metadata.source.RetainedOrbitCondition formula
      (Cell.neg
        (PeriodicCNF.clauseAnchor
          (metadataGaugedPositionedClause formula metadata).literals)) := by
  let anchorShift :=
    Cell.neg
      (PeriodicCNF.clauseAnchor
        (metadataGaugedPositionedClause formula metadata).literals)
  have sourceMember :
      metadata.source.RetainedComponentMember formula :=
    (metadata.retainedValid_iff_sourceMember_and_localClauseMember
      formula).mp valid |>.1
  cases sourceEq : metadata.source with
  | crossover crossing localClauseIndex =>
      rw [← sourceEq]
      change metadata.source.RetainedOrbitCondition formula anchorShift
      apply
        metadata.source.retainedOrbitCondition_of_periodTranslate_mem
          formula sourceMember anchorShift
      simpa only [anchorShift] using
        (metadata.crossover_anchorNormalize_retainedComponentMember
          wellFormed degree isLocal valid nonempty
          crossing localClauseIndex sourceEq)
  | carrier link localClauseIndex =>
      exfalso
      apply notCarrier
      refine ⟨link, ?_⟩
      rw [sourceEq]
      rfl
  | bend routeBend localClauseIndex =>
      rw [← sourceEq]
      change metadata.source.RetainedOrbitCondition formula anchorShift
      apply
        metadata.source.retainedOrbitCondition_of_periodTranslate_mem
          formula sourceMember anchorShift
      simpa only [anchorShift] using
        (metadata.bend_anchorNormalize_retainedComponentMember
          wellFormed degree isLocal valid nonempty
          routeBend localClauseIndex sourceEq)
  | routedClause site =>
      rw [← sourceEq]
      change metadata.source.RetainedOrbitCondition formula anchorShift
      apply
        metadata.source.retainedOrbitCondition_of_periodTranslate_mem
          formula sourceMember anchorShift
      simpa only [anchorShift] using
        (metadata.routedClause_anchorNormalize_retainedComponentMember
          wellFormed degree isLocal valid nonempty site sourceEq)
  | routedVariable site armIndex arm link localClauseIndex =>
      rw [← sourceEq]
      simpa only [anchorShift] using
        (metadata.routedVariable_anchorNormalize_retainedOrbitCondition
          wellFormed degree isLocal valid nonempty
          site armIndex arm link localClauseIndex sourceEq)

/-- The raw-carrier route-separation API also accepts the uniform
noncarrier orbit condition.  The condition may choose a different retained
source presentation with the same translated component; this is essential
for routed-variable arms whose sorted finite index changes at a halo
boundary. -/
theorem
    DrawingPlanarSATClauseMetadata.two_periodTranslate_localRoutes_avoidEachOther_of_raw_carrier_retainedOrbitCondition
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (first second : DrawingPlanarSATClauseMetadata Variable)
    (firstValid : first.RetainedValid formula)
    (secondValid : second.RetainedValid formula)
    (firstShift secondShift : Cell)
    (link : EqualityLink CarrierNode)
    (localClauseIndex : Nat)
    (firstSourceEq :
      first.source = .carrier link localClauseIndex)
    (translatedLinkMember :
      carrierLinkPeriodTranslate formula.incidenceGraph link firstShift ∈
        retainedDrawingCompleteCarrierLinksRaw
          formula.incidenceGraph)
    (translatedFirstNeighbor :
      IsNeighborTranslation
        ((carrierLinkPeriodTranslate formula.incidenceGraph
          link firstShift).first.translate))
    (secondCondition :
      second.source.RetainedOrbitCondition formula secondShift)
    {firstLiteral secondLiteral :
      PlanarSATVariable Variable × Bool}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        first.clause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        second.clause.literals.zipIdx)
    (secondNotCarrier :
      ¬∃ secondLink,
        second.source.component = .carrier secondLink) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (((first.source.periodTranslate formula firstShift).incidenceDrawing
        formula).routes
          first.source.localClauseIndex firstLiteralIndex)
      (((second.source.periodTranslate formula secondShift).incidenceDrawing
        formula).routes
          second.source.localClauseIndex secondLiteralIndex) := by
  have secondSourceMember :
      second.source.RetainedComponentMember formula :=
    (second.retainedValid_iff_sourceMember_and_localClauseMember
      formula).mp secondValid |>.1
  rcases
      second.source.exists_retainedTarget_periodTranslate
        formula degree secondSourceMember secondShift
        secondCondition with
    ⟨targetSource, targetSourceMember,
      targetComponentEq, targetLocalClauseIndexEq⟩
  have secondLocalClauseMember :
      (second.clause, second.source.localClauseIndex) ∈
        (second.source.clauseFormula formula).zipIdx :=
    (second.retainedValid_iff_sourceMember_and_localClauseMember
      formula).mp secondValid |>.2
  rcases
      second.source.exists_periodTranslatedClauseLiteral
        formula secondShift second.clause secondLocalClauseMember
        secondLiteral secondLiteralIndex secondLiteralMember with
    ⟨targetClause, targetLiteral,
      translatedClauseMember, targetLiteralMember⟩
  let translatedSource :=
    second.source.periodTranslate formula secondShift
  let targetMetadata :
      DrawingPlanarSATClauseMetadata Variable :=
    ⟨targetClause, targetSource⟩
  have targetFormulaEq :
      targetSource.clauseFormula formula =
        translatedSource.clauseFormula formula :=
    targetSource.clauseFormula_eq_of_component_eq
      formula translatedSource targetComponentEq
  have translatedLocalClauseIndexEq :
      translatedSource.localClauseIndex =
        second.source.localClauseIndex :=
    DrawingPlanarSATClauseSource.localClauseIndex_periodTranslate
      formula second.source secondShift
  have targetClauseMember :
      (targetClause, targetSource.localClauseIndex) ∈
        (targetSource.clauseFormula formula).zipIdx := by
    rw [targetFormulaEq, targetLocalClauseIndexEq,
      ← translatedLocalClauseIndexEq]
    exact translatedClauseMember
  have targetValid :
      targetMetadata.RetainedValid formula := by
    apply
      (targetMetadata
        |>.retainedValid_iff_sourceMember_and_localClauseMember
          formula).mpr
    exact ⟨targetSourceMember, targetClauseMember⟩
  have targetNotCarrier :
      ¬∃ targetLink,
        targetMetadata.source.component = .carrier targetLink := by
    rintro ⟨targetLink, targetCarrierEq⟩
    apply secondNotCarrier
    have translatedCarrierEq :
        translatedSource.component = .carrier targetLink :=
      targetComponentEq.symm.trans targetCarrierEq
    rcases second with ⟨secondClause, secondSource⟩
    cases secondSource <;>
      simp_all [translatedSource,
        DrawingPlanarSATClauseSource.periodTranslate,
        DrawingPlanarSATClauseSource.component]
  have avoid :=
    first.periodTranslate_localRoutes_avoidEachOther_of_raw_carrier
      wellFormed degree isLocal targetMetadata
      firstValid targetValid firstShift
      link localClauseIndex firstSourceEq
      translatedLinkMember translatedFirstNeighbor
      firstLiteralMember targetLiteralMember targetNotCarrier
  have targetDrawingEq :
      targetSource.incidenceDrawing formula =
        translatedSource.incidenceDrawing formula :=
    targetSource.incidenceDrawing_eq_of_component_eq
      formula translatedSource targetComponentEq
  simpa only [targetMetadata, targetDrawingEq,
    targetLocalClauseIndexEq, translatedSource,
    translatedLocalClauseIndexEq] using avoid

/-- A contact with an anchor-normalized final carrier segment forces a
translated routed-clause source to remain in the neighboring retained
site family. -/
theorem
    FinalGaugedSegmentOccurrenceWitness.translated_routedClause_retained_of_contact
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {firstIndexed secondIndexed : IndexedGridSegment}
    (firstMember :
      firstIndexed ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).indexedSegments)
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (site : ClauseRouteSite)
    (secondSourceEq :
      second.routeWitness.metadata.source = .routedClause site)
    (meet :
      GridSegment.InteriorsMeet
        (firstIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift))
        (secondIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift))) :
    (second.routeWitness.metadata.source.periodTranslate formula
      (Cell.sub second.physicalShift firstShift)
        |>.RetainedComponentMember formula) := by
  let graph := formula.incidenceGraph
  let sourceShift := Cell.sub second.physicalShift firstShift
  have secondNotCarrier :
      ¬∃ link,
        second.routeWitness.metadata.source.component =
          DrawingPlanarSATComponent.carrier link := by
    rintro ⟨link, componentEq⟩
    rw [secondSourceEq] at componentEq
    simp [DrawingPlanarSATClauseSource.component] at componentEq
  have siteMember :
      site ∈ drawingClauseRouteSites formula := by
    have sourceMember := second.source_retainedComponentMember
    rw [secondSourceEq] at sourceMember
    exact sourceMember
  have centerEq :
      second.routeWitness.metadata.source.component.macrocellCenter
          formula =
        some
          (liftedIncidenceVertexPosition
            formula (.clause site.1) site.2) := by
    rw [secondSourceEq]
    rfl
  have translatedEndpoints :=
    second.translatedPhysicalSegment_endpoints_in_macrocell
      wellFormed degree isLocal secondNotCarrier
      (liftedIncidenceVertexPosition
        formula (.clause site.1) site.2)
      centerEq sourceShift
  rw [liftedIncidenceVertexPosition_add_periodTranslation
    formula (.clause site.1) site.2 sourceShift] at translatedEndpoints
  have finalEndpointBounds :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_segmentEndpointsInExpandedSquare
      formula wellFormed degree isLocal clausesNonempty
      firstIndexed firstMember
  have expandedStart :
      let period : Int :=
        planarMacroScale * drawingGridSize graph;
      -period < firstIndexed.segment.start.1 ∧
        firstIndexed.segment.start.1 < 2 * period ∧
        -period < firstIndexed.segment.start.2 ∧
        firstIndexed.segment.start.2 < 2 * period := by
    simpa only [PeriodicGridDrawing.PositionInExpandedSquare,
      graph,
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_gridSize_int]
      using finalEndpointBounds.1
  have expandedFinish :
      let period : Int :=
        planarMacroScale * drawingGridSize graph;
      -period < firstIndexed.segment.finish.1 ∧
        firstIndexed.segment.finish.1 < 2 * period ∧
        -period < firstIndexed.segment.finish.2 ∧
        firstIndexed.segment.finish.2 < 2 * period := by
    simpa only [PeriodicGridDrawing.PositionInExpandedSquare,
      graph,
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_gridSize_int]
      using finalEndpointBounds.2
  have aligned :=
    first.anchorAlignedPhysical_interiorsMeet_of_final second meet
  have translatedNeighbor :
      IsNeighborTranslation (Cell.add site.2 sourceShift) := by
    exact
      liftedDrawingVertexPosition_translate_neighbor_of_macrocellSegment_meets_expanded
        graph
        (drawingClauseRouteSite_vertex_mem formula siteMember)
        (Cell.add site.2 sourceShift)
        firstIndexed.segment
        (second.physicalSegment.translate
          (carrierMacroPeriodTranslation graph sourceShift))
        expandedStart expandedFinish
        translatedEndpoints.1 translatedEndpoints.2 aligned
  rw [secondSourceEq]
  exact
    routedClauseSource_periodTranslate_retainedComponentMember_of_neighbor
      formula site siteMember sourceShift translatedNeighbor

/-- A retained carrier metadata source supplies the raw-link membership and
neighboring first occurrence required by the finite carrier separation API. -/
theorem
    FinalGaugedSegmentOccurrenceWitness.carrier_source_raw_and_neighbor
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {indexed : IndexedGridSegment}
    {shift : Cell}
    (witness :
      FinalGaugedSegmentOccurrenceWitness formula indexed shift)
    (link : EqualityLink CarrierNode)
    (componentEq :
      witness.routeWitness.metadata.source.component = .carrier link) :
    link ∈
        retainedDrawingCompleteCarrierLinksRaw formula.incidenceGraph ∧
      IsNeighborTranslation link.first.translate := by
  rcases
      witness.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq link componentEq with
    ⟨localClauseIndex, sourceEq⟩
  have sourceMember :=
    witness.source_retainedComponentMember
  rw [sourceEq] at sourceMember
  have selectedMember :
      link ∈
        retainedDrawingCompleteCarrierLinks formula.incidenceGraph := by
    simpa only [
      DrawingPlanarSATClauseSource.RetainedComponentMember] using
      sourceMember
  exact
    ⟨((mem_retainedDrawingCompleteCarrierLinks_iff
        formula.incidenceGraph link).mp selectedMember).1,
      retainedDrawingCompleteCarrierLink_first_translate_neighbor
        formula.incidenceGraph selectedMember⟩

/-- The common-shift raw-carrier bridge with component-equivalent
noncarrier reindexing.  A noncarrier orbit condition is enough even when its
literal translated source is absent from the finite enumeration. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_noncarrier_of_common_raw_retainedOrbitCondition
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (firstSourceShift secondSourceShift : Cell)
    (commonShiftEq :
      Cell.sub first.physicalShift firstSourceShift =
        Cell.sub second.physicalShift secondSourceShift)
    (link : EqualityLink CarrierNode)
    (firstComponentEq :
      first.routeWitness.metadata.source.component = .carrier link)
    (secondNotCarrier :
      ¬∃ secondLink,
        second.routeWitness.metadata.source.component =
          .carrier secondLink)
    (translatedLinkMember :
      carrierLinkPeriodTranslate formula.incidenceGraph link
          firstSourceShift ∈
        retainedDrawingCompleteCarrierLinksRaw
          formula.incidenceGraph)
    (translatedFirstNeighbor :
      IsNeighborTranslation
        ((carrierLinkPeriodTranslate formula.incidenceGraph link
          firstSourceShift).first.translate))
    (translatedSecondCondition :
      second.routeWitness.metadata.source.RetainedOrbitCondition
        formula secondSourceShift) :
    ¬GridSegment.InteriorsMeet
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift))
      (secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)) := by
  rcases
      first.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq
          link firstComponentEq with
    ⟨localClauseIndex, firstSourceEq⟩
  have routeAvoid :=
    first.routeWitness.metadata
      |>.two_periodTranslate_localRoutes_avoidEachOther_of_raw_carrier_retainedOrbitCondition
        wellFormed degree isLocal second.routeWitness.metadata
        first.metadata_retainedValid second.metadata_retainedValid
        firstSourceShift secondSourceShift
        link localClauseIndex firstSourceEq
        translatedLinkMember translatedFirstNeighbor
        translatedSecondCondition
        first.routeWitness.literalMember
        second.routeWitness.literalMember secondNotCarrier
  exact
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_two_periodTranslate_localRoutesAvoidEachOther
      formula first second firstSourceShift secondSourceShift
      commonShiftEq routeAvoid

/-- The common-shift raw-carrier bridge with component-equivalent
noncarrier reindexing also preserves asymmetric interior-versus-closed
avoidance. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_carrier_noncarrier_of_common_raw_retainedOrbitCondition
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (firstSourceShift secondSourceShift : Cell)
    (commonShiftEq :
      Cell.sub first.physicalShift firstSourceShift =
        Cell.sub second.physicalShift secondSourceShift)
    (link : EqualityLink CarrierNode)
    (firstComponentEq :
      first.routeWitness.metadata.source.component = .carrier link)
    (secondNotCarrier :
      ¬∃ secondLink,
        second.routeWitness.metadata.source.component =
          .carrier secondLink)
    (translatedLinkMember :
      carrierLinkPeriodTranslate formula.incidenceGraph link
          firstSourceShift ∈
        retainedDrawingCompleteCarrierLinksRaw
          formula.incidenceGraph)
    (translatedFirstNeighbor :
      IsNeighborTranslation
        ((carrierLinkPeriodTranslate formula.incidenceGraph link
          firstSourceShift).first.translate))
    (translatedSecondCondition :
      second.routeWitness.metadata.source.RetainedOrbitCondition
        formula secondSourceShift)
    (point : Cell)
    (firstContains :
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift)).InteriorContains point) :
    ¬(secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)).Contains point := by
  rcases
      first.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq
          link firstComponentEq with
    ⟨localClauseIndex, firstSourceEq⟩
  have routeAvoid :=
    first.routeWitness.metadata
      |>.two_periodTranslate_localRoutes_avoidEachOther_of_raw_carrier_retainedOrbitCondition
        wellFormed degree isLocal second.routeWitness.metadata
        first.metadata_retainedValid second.metadata_retainedValid
        firstSourceShift secondSourceShift
        link localClauseIndex firstSourceEq
        translatedLinkMember translatedFirstNeighbor
        translatedSecondCondition
        first.routeWitness.literalMember
        second.routeWitness.literalMember secondNotCarrier
  apply
    retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_two_periodTranslate_localRoutesAvoidEachOther
      formula first second firstSourceShift secondSourceShift
      commonShiftEq routeAvoid
  exact firstContains

/-- A bounded relative displacement between one carrier occurrence
coordinate and one noncarrier source coordinate is enough for periodic
separation.  The displacement is split between the two finite sources, so
neither source is required to absorb the entire quotient translation.

The noncarrier family supplies only its one-coordinate closure rule.  Bends,
routed clauses, and routed-variable arms all have this form; crossovers need
the analogous two-coordinate balancing argument. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_noncarrier_of_balanced_source_coordinate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (link : EqualityLink CarrierNode)
    (firstComponentEq :
      first.routeWitness.metadata.source.component = .carrier link)
    (secondNotCarrier :
      ¬∃ secondLink,
        second.routeWitness.metadata.source.component =
          .carrier secondLink)
    (secondBase : Cell)
    (secondClosure :
      ∀ adjustment,
        IsNeighborTranslation (Cell.add secondBase adjustment) →
          second.routeWitness.metadata.source.RetainedOrbitCondition
            formula
            (Cell.add
              (Cell.neg second.sourceClauseAnchor)
              adjustment))
    (contactClose :
      GridSegment.InteriorsMeet
          (firstIndexed.segment.translate
            ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
              formula).periodTranslation firstShift))
          (secondIndexed.segment.translate
            ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
              formula).periodTranslation secondShift)) →
        Cell.sub
            (Cell.add
              (Cell.add link.first.translate
                (Cell.neg first.sourceClauseAnchor))
              (Cell.sub firstShift secondShift))
            secondBase ∈
          PeriodicGridDrawing.doubleNeighborTranslations) :
    ¬GridSegment.InteriorsMeet
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift))
      (secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)) := by
  let firstBase :=
    Cell.add link.first.translate
      (Cell.neg first.sourceClauseAnchor)
  let relative := Cell.sub firstShift secondShift
  intro meet
  rcases
      exists_neighbor_balancing_adjustments
        firstBase secondBase relative
        (by simpa only [firstBase, relative] using contactClose meet) with
    ⟨firstAdjustment, secondAdjustment,
      adjustmentDifference,
      translatedFirstNeighbor,
      translatedSecondNeighbor⟩
  let firstSourceShift :=
    Cell.add (Cell.neg first.sourceClauseAnchor)
      firstAdjustment
  let secondSourceShift :=
    Cell.add (Cell.neg second.sourceClauseAnchor)
      secondAdjustment
  have carrierData :=
    first.carrier_source_raw_and_neighbor link firstComponentEq
  have targetFirstNeighbor :
      IsNeighborTranslation
        ((carrierLinkPeriodTranslate formula.incidenceGraph
          link firstSourceShift).first.translate) := by
    simpa [firstBase, firstSourceShift,
      CarrierNode.translate_periodTranslate,
      Cell.add, Cell.neg, Cell.sub, add_assoc] using
        translatedFirstNeighbor
  have translatedLinkMember :
      carrierLinkPeriodTranslate formula.incidenceGraph
          link firstSourceShift ∈
        retainedDrawingCompleteCarrierLinksRaw
          formula.incidenceGraph :=
    retainedDrawingCompleteCarrierLinkRaw_periodTranslate_mem
      wellFormed degree isLocal carrierData.1
      firstSourceShift carrierData.2 targetFirstNeighbor
  have translatedSecondCondition :
      second.routeWitness.metadata.source.RetainedOrbitCondition
        formula secondSourceShift := by
    exact secondClosure secondAdjustment translatedSecondNeighbor
  have commonShiftEq :
      Cell.sub first.physicalShift firstSourceShift =
        Cell.sub second.physicalShift secondSourceShift := by
    rcases firstShift with ⟨firstX, firstY⟩
    rcases secondShift with ⟨secondX, secondY⟩
    rcases first.sourceClauseAnchor with
      ⟨firstAnchorX, firstAnchorY⟩
    rcases second.sourceClauseAnchor with
      ⟨secondAnchorX, secondAnchorY⟩
    rcases firstAdjustment with
      ⟨firstAdjustmentX, firstAdjustmentY⟩
    rcases secondAdjustment with
      ⟨secondAdjustmentX, secondAdjustmentY⟩
    simp only [FinalGaugedSegmentOccurrenceWitness.physicalShift_eq,
      firstSourceShift, secondSourceShift, relative,
      Cell.sub, Cell.add, Cell.neg, Prod.mk.injEq] at adjustmentDifference ⊢
    constructor <;> omega
  exact
    (retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_noncarrier_of_common_raw_retainedOrbitCondition
      formula wellFormed degree isLocal first second
      firstSourceShift secondSourceShift commonShiftEq
      link firstComponentEq secondNotCarrier
      translatedLinkMember targetFirstNeighbor
      translatedSecondCondition)
      meet

/-- Endpoint-aware balanced raw-carrier separation when the noncarrier
orbit condition has one occurrence coordinate. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_carrier_noncarrier_of_balanced_source_coordinate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (link : EqualityLink CarrierNode)
    (firstComponentEq :
      first.routeWitness.metadata.source.component = .carrier link)
    (secondNotCarrier :
      ¬∃ secondLink,
        second.routeWitness.metadata.source.component =
          .carrier secondLink)
    (secondBase : Cell)
    (secondClosure :
      ∀ adjustment,
        IsNeighborTranslation (Cell.add secondBase adjustment) →
          second.routeWitness.metadata.source.RetainedOrbitCondition
            formula
            (Cell.add
              (Cell.neg second.sourceClauseAnchor)
              adjustment))
    (contactClose :
      ∀ point,
        (firstIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift)).InteriorContains
              point →
          (secondIndexed.segment.translate
            ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
              formula).periodTranslation secondShift)).Contains point →
            Cell.sub
                (Cell.add
                  (Cell.add link.first.translate
                    (Cell.neg first.sourceClauseAnchor))
                  (Cell.sub firstShift secondShift))
                secondBase ∈
              PeriodicGridDrawing.doubleNeighborTranslations)
    (point : Cell)
    (firstContains :
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift)).InteriorContains point) :
    ¬(secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)).Contains point := by
  let firstBase :=
    Cell.add link.first.translate
      (Cell.neg first.sourceClauseAnchor)
  let relative := Cell.sub firstShift secondShift
  intro secondContains
  rcases
      exists_neighbor_balancing_adjustments
        firstBase secondBase relative
        (by
          simpa only [firstBase, relative] using
            contactClose point firstContains secondContains) with
    ⟨firstAdjustment, secondAdjustment,
      adjustmentDifference,
      translatedFirstNeighbor,
      translatedSecondNeighbor⟩
  let firstSourceShift :=
    Cell.add (Cell.neg first.sourceClauseAnchor)
      firstAdjustment
  let secondSourceShift :=
    Cell.add (Cell.neg second.sourceClauseAnchor)
      secondAdjustment
  have carrierData :=
    first.carrier_source_raw_and_neighbor link firstComponentEq
  have targetFirstNeighbor :
      IsNeighborTranslation
        ((carrierLinkPeriodTranslate formula.incidenceGraph
          link firstSourceShift).first.translate) := by
    simpa [firstBase, firstSourceShift,
      CarrierNode.translate_periodTranslate,
      Cell.add, Cell.neg, Cell.sub, add_assoc] using
        translatedFirstNeighbor
  have translatedLinkMember :
      carrierLinkPeriodTranslate formula.incidenceGraph
          link firstSourceShift ∈
        retainedDrawingCompleteCarrierLinksRaw
          formula.incidenceGraph :=
    retainedDrawingCompleteCarrierLinkRaw_periodTranslate_mem
      wellFormed degree isLocal carrierData.1
      firstSourceShift carrierData.2 targetFirstNeighbor
  have translatedSecondCondition :
      second.routeWitness.metadata.source.RetainedOrbitCondition
        formula secondSourceShift := by
    exact secondClosure secondAdjustment translatedSecondNeighbor
  have commonShiftEq :
      Cell.sub first.physicalShift firstSourceShift =
        Cell.sub second.physicalShift secondSourceShift := by
    rcases firstShift with ⟨firstX, firstY⟩
    rcases secondShift with ⟨secondX, secondY⟩
    rcases first.sourceClauseAnchor with
      ⟨firstAnchorX, firstAnchorY⟩
    rcases second.sourceClauseAnchor with
      ⟨secondAnchorX, secondAnchorY⟩
    rcases firstAdjustment with
      ⟨firstAdjustmentX, firstAdjustmentY⟩
    rcases secondAdjustment with
      ⟨secondAdjustmentX, secondAdjustmentY⟩
    simp only [FinalGaugedSegmentOccurrenceWitness.physicalShift_eq,
      firstSourceShift, secondSourceShift, relative,
      Cell.sub, Cell.add, Cell.neg, Prod.mk.injEq] at adjustmentDifference ⊢
    constructor <;> omega
  exact
    (retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_carrier_noncarrier_of_common_raw_retainedOrbitCondition
      formula wellFormed degree isLocal first second
      firstSourceShift secondSourceShift commonShiftEq
      link firstComponentEq secondNotCarrier
      translatedLinkMember targetFirstNeighbor
      translatedSecondCondition
      point firstContains)
      secondContains

/-- Balanced raw-carrier separation when the noncarrier orbit condition has
two occurrence coordinates sharing one source adjustment. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_noncarrier_of_balanced_two_source_coordinates
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (link : EqualityLink CarrierNode)
    (firstComponentEq :
      first.routeWitness.metadata.source.component = .carrier link)
    (secondNotCarrier :
      ¬∃ secondLink,
        second.routeWitness.metadata.source.component =
          .carrier secondLink)
    (secondFirstBase secondSecondBase : Cell)
    (secondBasesClose :
      Cell.sub secondFirstBase secondSecondBase ∈
        PeriodicGridDrawing.doubleNeighborTranslations)
    (secondClosure :
      ∀ adjustment,
        IsNeighborTranslation
            (Cell.add secondFirstBase adjustment) →
          IsNeighborTranslation
            (Cell.add secondSecondBase adjustment) →
          second.routeWitness.metadata.source.RetainedOrbitCondition
            formula
            (Cell.add
              (Cell.neg second.sourceClauseAnchor)
              adjustment))
    (contactClose :
      GridSegment.InteriorsMeet
          (firstIndexed.segment.translate
            ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
              formula).periodTranslation firstShift))
          (secondIndexed.segment.translate
            ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
              formula).periodTranslation secondShift)) →
        Cell.sub
            (Cell.add
              (Cell.add link.first.translate
                (Cell.neg first.sourceClauseAnchor))
              (Cell.sub firstShift secondShift))
            secondFirstBase ∈
              PeriodicGridDrawing.doubleNeighborTranslations ∧
          Cell.sub
              (Cell.add
                (Cell.add link.first.translate
                  (Cell.neg first.sourceClauseAnchor))
                (Cell.sub firstShift secondShift))
              secondSecondBase ∈
            PeriodicGridDrawing.doubleNeighborTranslations) :
    ¬GridSegment.InteriorsMeet
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift))
      (secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)) := by
  let firstBase :=
    Cell.add link.first.translate
      (Cell.neg first.sourceClauseAnchor)
  let relative := Cell.sub firstShift secondShift
  intro meet
  have contactBounds := contactClose meet
  rcases
      exists_neighbor_balancing_adjustments_two_second_bases
        firstBase secondFirstBase secondSecondBase relative
        (by simpa only [firstBase, relative] using contactBounds.1)
        (by simpa only [firstBase, relative] using contactBounds.2)
        secondBasesClose with
    ⟨firstAdjustment, secondAdjustment,
      adjustmentDifference,
      translatedFirstNeighbor,
      translatedSecondFirstNeighbor,
      translatedSecondSecondNeighbor⟩
  let firstSourceShift :=
    Cell.add (Cell.neg first.sourceClauseAnchor)
      firstAdjustment
  let secondSourceShift :=
    Cell.add (Cell.neg second.sourceClauseAnchor)
      secondAdjustment
  have carrierData :=
    first.carrier_source_raw_and_neighbor link firstComponentEq
  have targetFirstNeighbor :
      IsNeighborTranslation
        ((carrierLinkPeriodTranslate formula.incidenceGraph
          link firstSourceShift).first.translate) := by
    simpa [firstBase, firstSourceShift,
      CarrierNode.translate_periodTranslate,
      Cell.add, Cell.neg, Cell.sub, add_assoc] using
        translatedFirstNeighbor
  have translatedLinkMember :
      carrierLinkPeriodTranslate formula.incidenceGraph
          link firstSourceShift ∈
        retainedDrawingCompleteCarrierLinksRaw
          formula.incidenceGraph :=
    retainedDrawingCompleteCarrierLinkRaw_periodTranslate_mem
      wellFormed degree isLocal carrierData.1
      firstSourceShift carrierData.2 targetFirstNeighbor
  have translatedSecondCondition :
      second.routeWitness.metadata.source.RetainedOrbitCondition
        formula secondSourceShift := by
    exact secondClosure secondAdjustment
      translatedSecondFirstNeighbor
      translatedSecondSecondNeighbor
  have commonShiftEq :
      Cell.sub first.physicalShift firstSourceShift =
        Cell.sub second.physicalShift secondSourceShift := by
    rcases firstShift with ⟨firstX, firstY⟩
    rcases secondShift with ⟨secondX, secondY⟩
    rcases first.sourceClauseAnchor with
      ⟨firstAnchorX, firstAnchorY⟩
    rcases second.sourceClauseAnchor with
      ⟨secondAnchorX, secondAnchorY⟩
    rcases firstAdjustment with
      ⟨firstAdjustmentX, firstAdjustmentY⟩
    rcases secondAdjustment with
      ⟨secondAdjustmentX, secondAdjustmentY⟩
    simp only [FinalGaugedSegmentOccurrenceWitness.physicalShift_eq,
      firstSourceShift, secondSourceShift, relative,
      Cell.sub, Cell.add, Cell.neg, Prod.mk.injEq] at adjustmentDifference ⊢
    constructor <;> omega
  exact
    (retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_noncarrier_of_common_raw_retainedOrbitCondition
      formula wellFormed degree isLocal first second
      firstSourceShift secondSourceShift commonShiftEq
      link firstComponentEq secondNotCarrier
      translatedLinkMember targetFirstNeighbor
      translatedSecondCondition)
      meet

/-- Endpoint-aware balanced raw-carrier separation when the noncarrier
orbit condition has two occurrence coordinates sharing one source
adjustment. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_carrier_noncarrier_of_balanced_two_source_coordinates
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (link : EqualityLink CarrierNode)
    (firstComponentEq :
      first.routeWitness.metadata.source.component = .carrier link)
    (secondNotCarrier :
      ¬∃ secondLink,
        second.routeWitness.metadata.source.component =
          .carrier secondLink)
    (secondFirstBase secondSecondBase : Cell)
    (secondBasesClose :
      Cell.sub secondFirstBase secondSecondBase ∈
        PeriodicGridDrawing.doubleNeighborTranslations)
    (secondClosure :
      ∀ adjustment,
        IsNeighborTranslation
            (Cell.add secondFirstBase adjustment) →
          IsNeighborTranslation
            (Cell.add secondSecondBase adjustment) →
          second.routeWitness.metadata.source.RetainedOrbitCondition
            formula
            (Cell.add
              (Cell.neg second.sourceClauseAnchor)
              adjustment))
    (contactClose :
      ∀ point,
        (firstIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift)).InteriorContains
              point →
          (secondIndexed.segment.translate
            ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
              formula).periodTranslation secondShift)).Contains point →
            Cell.sub
                (Cell.add
                  (Cell.add link.first.translate
                    (Cell.neg first.sourceClauseAnchor))
                  (Cell.sub firstShift secondShift))
                secondFirstBase ∈
                PeriodicGridDrawing.doubleNeighborTranslations ∧
              Cell.sub
                  (Cell.add
                    (Cell.add link.first.translate
                      (Cell.neg first.sourceClauseAnchor))
                    (Cell.sub firstShift secondShift))
                  secondSecondBase ∈
                PeriodicGridDrawing.doubleNeighborTranslations)
    (point : Cell)
    (firstContains :
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift)).InteriorContains point) :
    ¬(secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)).Contains point := by
  let firstBase :=
    Cell.add link.first.translate
      (Cell.neg first.sourceClauseAnchor)
  let relative := Cell.sub firstShift secondShift
  intro secondContains
  have contactBounds := contactClose point firstContains secondContains
  rcases
      exists_neighbor_balancing_adjustments_two_second_bases
        firstBase secondFirstBase secondSecondBase relative
        (by simpa only [firstBase, relative] using contactBounds.1)
        (by simpa only [firstBase, relative] using contactBounds.2)
        secondBasesClose with
    ⟨firstAdjustment, secondAdjustment,
      adjustmentDifference,
      translatedFirstNeighbor,
      translatedSecondFirstNeighbor,
      translatedSecondSecondNeighbor⟩
  let firstSourceShift :=
    Cell.add (Cell.neg first.sourceClauseAnchor)
      firstAdjustment
  let secondSourceShift :=
    Cell.add (Cell.neg second.sourceClauseAnchor)
      secondAdjustment
  have carrierData :=
    first.carrier_source_raw_and_neighbor link firstComponentEq
  have targetFirstNeighbor :
      IsNeighborTranslation
        ((carrierLinkPeriodTranslate formula.incidenceGraph
          link firstSourceShift).first.translate) := by
    simpa [firstBase, firstSourceShift,
      CarrierNode.translate_periodTranslate,
      Cell.add, Cell.neg, Cell.sub, add_assoc] using
        translatedFirstNeighbor
  have translatedLinkMember :
      carrierLinkPeriodTranslate formula.incidenceGraph
          link firstSourceShift ∈
        retainedDrawingCompleteCarrierLinksRaw
          formula.incidenceGraph :=
    retainedDrawingCompleteCarrierLinkRaw_periodTranslate_mem
      wellFormed degree isLocal carrierData.1
      firstSourceShift carrierData.2 targetFirstNeighbor
  have translatedSecondCondition :
      second.routeWitness.metadata.source.RetainedOrbitCondition
        formula secondSourceShift := by
    exact secondClosure secondAdjustment
      translatedSecondFirstNeighbor
      translatedSecondSecondNeighbor
  have commonShiftEq :
      Cell.sub first.physicalShift firstSourceShift =
        Cell.sub second.physicalShift secondSourceShift := by
    rcases firstShift with ⟨firstX, firstY⟩
    rcases secondShift with ⟨secondX, secondY⟩
    rcases first.sourceClauseAnchor with
      ⟨firstAnchorX, firstAnchorY⟩
    rcases second.sourceClauseAnchor with
      ⟨secondAnchorX, secondAnchorY⟩
    rcases firstAdjustment with
      ⟨firstAdjustmentX, firstAdjustmentY⟩
    rcases secondAdjustment with
      ⟨secondAdjustmentX, secondAdjustmentY⟩
    simp only [FinalGaugedSegmentOccurrenceWitness.physicalShift_eq,
      firstSourceShift, secondSourceShift, relative,
      Cell.sub, Cell.add, Cell.neg, Prod.mk.injEq] at adjustmentDifference ⊢
    constructor <;> omega
  exact
    (retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_carrier_noncarrier_of_common_raw_retainedOrbitCondition
      formula wellFormed degree isLocal first second
      firstSourceShift secondSourceShift commonShiftEq
      link firstComponentEq secondNotCarrier
      translatedLinkMember targetFirstNeighbor
      translatedSecondCondition
      point firstContains)
      secondContains

/-- Anchor-normalizing the carrier source and translating the noncarrier
source by its physical shift minus the carrier's final shift leaves the same
external translate on both finite routes.  Retention of that translated
noncarrier therefore contradicts raw-carrier planarity. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_anchor_carrier_noncarrier_of_contact_retained
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (link : EqualityLink CarrierNode)
    (firstComponentEq :
      first.routeWitness.metadata.source.component = .carrier link)
    (secondNotCarrier :
      ¬∃ secondLink,
        second.routeWitness.metadata.source.component =
          .carrier secondLink)
    (contactRetained :
      GridSegment.InteriorsMeet
          (firstIndexed.segment.translate
            ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
              formula).periodTranslation firstShift))
          (secondIndexed.segment.translate
            ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
              formula).periodTranslation secondShift)) →
        (second.routeWitness.metadata.source.periodTranslate formula
          (Cell.sub second.physicalShift firstShift)
            |>.RetainedComponentMember formula)) :
    ¬GridSegment.InteriorsMeet
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift))
      (secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)) := by
  rcases
      first.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq link firstComponentEq with
    ⟨localClauseIndex, firstSourceEq⟩
  have firstNonempty :
      first.routeWitness.metadata.clause.literals ≠ [] := by
    intro empty
    have literalMember := first.routeWitness.literalMember
    rw [empty] at literalMember
    simp at literalMember
  let carrierShift := Cell.neg first.sourceClauseAnchor
  let secondSourceShift := Cell.sub second.physicalShift firstShift
  have translatedLinkMember :
      carrierLinkPeriodTranslate formula.incidenceGraph link carrierShift ∈
        retainedDrawingCompleteCarrierLinksRaw formula.incidenceGraph := by
    exact
      first.routeWitness.metadata.carrier_anchorNormalize_mem_raw
        wellFormed degree isLocal first.metadata_retainedValid
        firstNonempty link localClauseIndex firstSourceEq
  have translatedFirstNeighbor :
      IsNeighborTranslation
        ((carrierLinkPeriodTranslate formula.incidenceGraph
          link carrierShift).first.translate) := by
    exact
      first.routeWitness.metadata.carrier_first_anchorNormalize_translate_neighbor
        wellFormed degree isLocal first.metadata_retainedValid
        firstNonempty link localClauseIndex firstSourceEq
  have commonShiftEq :
      Cell.sub first.physicalShift carrierShift =
        Cell.sub second.physicalShift secondSourceShift := by
    have firstCommon :
        Cell.sub first.physicalShift carrierShift = firstShift := by
      rcases firstShift with ⟨firstX, firstY⟩
      simp [carrierShift,
        FinalGaugedSegmentOccurrenceWitness.physicalShift_eq,
        Cell.sub, Cell.neg]
    have secondCommon :
        Cell.sub second.physicalShift secondSourceShift =
          firstShift := by
      have cellSubSelf (cell base : Cell) :
          Cell.sub cell (Cell.sub cell base) = base := by
        rcases cell with ⟨cellX, cellY⟩
        rcases base with ⟨baseX, baseY⟩
        simp [Cell.sub]
      exact cellSubSelf second.physicalShift firstShift
    rw [firstCommon, secondCommon]
  intro meet
  exact
    (retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_noncarrier_of_common_raw
      formula wellFormed degree isLocal first second
      carrierShift secondSourceShift commonShiftEq
      link firstComponentEq secondNotCarrier
      translatedLinkMember translatedFirstNeighbor
      (contactRetained meet))
      meet

/-- Final carrier segments have disjoint interiors from every routed-clause
segment occurrence, at arbitrary quotient translates. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_routedClause
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {firstIndexed secondIndexed : IndexedGridSegment}
    (firstMember :
      firstIndexed ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).indexedSegments)
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (link : EqualityLink CarrierNode)
    (firstComponentEq :
      first.routeWitness.metadata.source.component = .carrier link)
    (site : ClauseRouteSite)
    (secondSourceEq :
      second.routeWitness.metadata.source = .routedClause site) :
    ¬GridSegment.InteriorsMeet
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift))
      (secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)) := by
  have secondNotCarrier :
      ¬∃ secondLink,
        second.routeWitness.metadata.source.component =
          .carrier secondLink := by
    rintro ⟨secondLink, componentEq⟩
    rw [secondSourceEq] at componentEq
    simp [DrawingPlanarSATClauseSource.component] at componentEq
  have siteMember :
      site ∈ drawingClauseRouteSites formula := by
    have sourceMember := second.source_retainedComponentMember
    rw [secondSourceEq] at sourceMember
    exact sourceMember
  have firstNonempty :
      first.routeWitness.metadata.clause.literals ≠ [] := by
    intro empty
    have literalMember := first.routeWitness.literalMember
    rw [empty] at literalMember
    simp at literalMember
  have secondNonempty :
      second.routeWitness.metadata.clause.literals ≠ [] := by
    intro empty
    have literalMember := second.routeWitness.literalMember
    rw [empty] at literalMember
    simp at literalMember
  have secondCenterEq :
      second.routeWitness.metadata.source.component.macrocellCenter
          formula =
        some
          (liftedIncidenceVertexPosition
            formula (.clause site.1) site.2) := by
    rw [secondSourceEq]
    rfl
  have secondAnchorEq :
      second.sourceClauseAnchor = site.2 := by
    simpa only [
      FinalGaugedSegmentOccurrenceWitness.sourceClauseAnchor] using
      (second.routeWitness.metadata
        |>.sourceClauseAnchor_eq_liftedVertexTranslate
          wellFormed degree isLocal second.metadata_retainedValid
          secondNonempty (.clause site.1)
          (drawingClauseRouteSite_vertex_mem formula siteMember)
          site.2 secondCenterEq)
  apply
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_noncarrier_of_balanced_source_coordinate
      formula wellFormed degree isLocal first second
      link firstComponentEq secondNotCarrier (0, 0)
  · intro adjustment adjustmentNeighbor
    rw [secondSourceEq]
    change
      IsNeighborTranslation
        (Cell.add site.2
          (Cell.add
            (Cell.neg second.sourceClauseAnchor)
            adjustment))
    have translatedSiteEq :
        Cell.add site.2
            (Cell.add
              (Cell.neg second.sourceClauseAnchor)
              adjustment) =
          adjustment := by
      rw [secondAnchorEq]
      rcases site.2 with ⟨siteX, siteY⟩
      rcases adjustment with
        ⟨adjustmentX, adjustmentY⟩
      simp [Cell.add, Cell.neg, Cell.sub]
    rw [translatedSiteEq]
    simpa [Cell.add] using adjustmentNeighbor
  · intro meet
    rcases
        first.routeWitness.metadata.source
          |>.exists_eq_carrier_of_component_eq
            link firstComponentEq with
      ⟨localClauseIndex, firstSourceEq⟩
    have firstBaseNeighbor :
        IsNeighborTranslation
          (Cell.add link.first.translate
            (Cell.neg first.sourceClauseAnchor)) := by
      simpa only [
        FinalGaugedSegmentOccurrenceWitness.sourceClauseAnchor,
        carrierLinkPeriodTranslate_first,
        CarrierNode.translate_periodTranslate] using
        (first.routeWitness.metadata
          |>.carrier_first_anchorNormalize_translate_neighbor
            wellFormed degree isLocal first.metadata_retainedValid
            firstNonempty link localClauseIndex firstSourceEq)
    have firstEndpointBounds :=
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_segmentEndpointsInExpandedSquare
        formula wellFormed degree isLocal clausesNonempty
        firstIndexed firstMember
    have secondEndpointBounds :=
      second.endpointsInHalfOpenFundamentalSquare_of_not_carrier
        formula wellFormed degree isLocal clausesNonempty
        secondNotCarrier
    have relativeNeighbor :
        IsNeighborTranslation (Cell.sub firstShift secondShift) := by
      exact
        (mem_neighborTranslations_iff _).mp
          (PeriodicGridDrawing.relativeTranslate_isNeighbor_of_interiorsMeet_of_secondHalfOpen
            firstEndpointBounds secondEndpointBounds meet)
    have sumMember :=
      firstBaseNeighbor.add_mem_doubleNeighborTranslations
        relativeNeighbor
    simpa [Cell.sub] using sumMember

/-- Carrier--crossover separation reduces to doubled-halo bounds from the
anchor-normalized carrier occurrence to both anchor-normalized crossing
occurrences.  The two crossing occurrences remain coupled by one source
translation. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_crossover_of_contact_close
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (link : EqualityLink CarrierNode)
    (firstComponentEq :
      first.routeWitness.metadata.source.component = .carrier link)
    (crossing : CrossingRecord)
    (localClauseIndex : Nat)
    (secondSourceEq :
      second.routeWitness.metadata.source =
        .crossover crossing localClauseIndex)
    (contactClose :
      GridSegment.InteriorsMeet
          (firstIndexed.segment.translate
            ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
              formula).periodTranslation firstShift))
          (secondIndexed.segment.translate
            ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
              formula).periodTranslation secondShift)) →
        Cell.sub
            (Cell.add
              (Cell.add link.first.translate
                (Cell.neg first.sourceClauseAnchor))
              (Cell.sub firstShift secondShift))
            (Cell.add crossing.firstTranslate
              (Cell.neg second.sourceClauseAnchor)) ∈
            PeriodicGridDrawing.doubleNeighborTranslations ∧
          Cell.sub
              (Cell.add
                (Cell.add link.first.translate
                  (Cell.neg first.sourceClauseAnchor))
                (Cell.sub firstShift secondShift))
              (Cell.add crossing.secondTranslate
                (Cell.neg second.sourceClauseAnchor)) ∈
            PeriodicGridDrawing.doubleNeighborTranslations) :
    ¬GridSegment.InteriorsMeet
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift))
      (secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)) := by
  have secondNotCarrier :
      ¬∃ secondLink,
        second.routeWitness.metadata.source.component =
          .carrier secondLink := by
    rintro ⟨secondLink, componentEq⟩
    rw [secondSourceEq] at componentEq
    simp [DrawingPlanarSATClauseSource.component] at componentEq
  have secondNonempty :
      second.routeWitness.metadata.clause.literals ≠ [] := by
    intro empty
    have literalMember := second.routeWitness.literalMember
    rw [empty] at literalMember
    simp at literalMember
  have normalizedCondition :
      second.routeWitness.metadata.source.RetainedOrbitCondition
        formula (Cell.neg second.sourceClauseAnchor) := by
    simpa only [
      FinalGaugedSegmentOccurrenceWitness.sourceClauseAnchor] using
      (second.routeWitness.metadata
        |>.noncarrier_anchorNormalize_retainedOrbitCondition
          wellFormed degree isLocal second.metadata_retainedValid
          secondNonempty secondNotCarrier)
  have normalizedNeighbors :
      IsNeighborTranslation
          (Cell.add crossing.firstTranslate
            (Cell.neg second.sourceClauseAnchor)) ∧
        IsNeighborTranslation
          (Cell.add crossing.secondTranslate
            (Cell.neg second.sourceClauseAnchor)) := by
    rw [secondSourceEq] at normalizedCondition
    exact normalizedCondition
  have crossingBasesClose :
      Cell.sub
          (Cell.add crossing.firstTranslate
            (Cell.neg second.sourceClauseAnchor))
          (Cell.add crossing.secondTranslate
            (Cell.neg second.sourceClauseAnchor)) ∈
        PeriodicGridDrawing.doubleNeighborTranslations := by
    exact
      normalizedNeighbors.1.sub_mem_doubleNeighborTranslations
        normalizedNeighbors.2
  apply
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_noncarrier_of_balanced_two_source_coordinates
      formula wellFormed degree isLocal first second
      link firstComponentEq secondNotCarrier
      (Cell.add crossing.firstTranslate
        (Cell.neg second.sourceClauseAnchor))
      (Cell.add crossing.secondTranslate
        (Cell.neg second.sourceClauseAnchor))
      crossingBasesClose
  · intro adjustment firstNeighbor secondNeighbor
    rw [secondSourceEq]
    constructor
    · simpa [Cell.add, add_assoc] using firstNeighbor
    · simpa [Cell.add, add_assoc] using secondNeighbor
  · exact contactClose

/-- Every hypothetical carrier--crossover contact satisfies both doubled-halo
bounds required above: the translated crossing point lies on the carrier and
on each of the crossover's two supporting occurrences. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_crossover
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (link : EqualityLink CarrierNode)
    (firstComponentEq :
      first.routeWitness.metadata.source.component = .carrier link)
    (crossing : CrossingRecord)
    (localClauseIndex : Nat)
    (secondSourceEq :
      second.routeWitness.metadata.source =
        .crossover crossing localClauseIndex) :
    ¬GridSegment.InteriorsMeet
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift))
      (secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)) := by
  let graph := formula.incidenceGraph
  let anchorShift := Cell.neg first.sourceClauseAnchor
  let sourceShift := Cell.sub second.physicalShift firstShift
  let translatedLink :=
    carrierLinkPeriodTranslate graph link anchorShift
  let translatedCrossing :=
    crossing.periodTranslate graph sourceShift
  have secondNotCarrier :
      ¬∃ secondLink,
        second.routeWitness.metadata.source.component =
          .carrier secondLink := by
    rintro ⟨secondLink, componentEq⟩
    rw [secondSourceEq] at componentEq
    simp [DrawingPlanarSATClauseSource.component] at componentEq
  have crossingMember :
      crossing ∈ orientedCrossingHalo graph := by
    have sourceMember := second.source_retainedComponentMember
    rw [secondSourceEq] at sourceMember
    exact sourceMember
  have retainedCrossingMember :
      crossing ∈ retainedCrossings graph :=
    orientedCrossingHalo_subset_retainedCrossings
      wellFormed degree isLocal crossingMember
  have crossingSound :=
    retainedCrossings_sound graph retainedCrossingMember
  have centerEq :
      second.routeWitness.metadata.source.component.macrocellCenter
          formula =
        some crossing.point := by
    rw [secondSourceEq]
    rfl
  have carrierContains :=
    first.anchorNormalizedCarrier_supportingSegment_contains_translatedMacrocellCenter_of_contact
      formula wellFormed degree isLocal second
      link firstComponentEq secondNotCarrier
      crossing.point centerEq
  have firstInteriorContains :
      (translatedCrossing.firstSegment graph).InteriorContains
        translatedCrossing.point := by
    rw [CrossingRecord.firstSegment_periodTranslate]
    exact
      (PeriodicGridDrawing.interiorContains_translate_iff
        (crossing.firstSegment graph)
        ((drawing graph).periodTranslation sourceShift)
        crossing.point).mpr crossingSound.2.2.1
  have secondInteriorContains :
      (translatedCrossing.secondSegment graph).InteriorContains
        translatedCrossing.point := by
    rw [CrossingRecord.secondSegment_periodTranslate]
    exact
      (PeriodicGridDrawing.interiorContains_translate_iff
        (crossing.secondSegment graph)
        ((drawing graph).periodTranslation sourceShift)
        crossing.point).mpr crossingSound.2.2.2.1
  rcases
      first.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq
          link firstComponentEq with
    ⟨firstLocalClauseIndex, firstSourceEq⟩
  have firstNonempty :
      first.routeWitness.metadata.clause.literals ≠ [] := by
    intro empty
    have literalMember := first.routeWitness.literalMember
    rw [empty] at literalMember
    simp at literalMember
  have translatedLinkMember :
      translatedLink ∈
        retainedDrawingCompleteCarrierLinksRaw graph := by
    simpa only [translatedLink, graph, anchorShift,
      FinalGaugedSegmentOccurrenceWitness.sourceClauseAnchor] using
      (first.routeWitness.metadata
        |>.carrier_anchorNormalize_mem_raw
          wellFormed degree isLocal first.metadata_retainedValid
          firstNonempty link firstLocalClauseIndex firstSourceEq)
  have carrierIndexedMember :
      translatedLink.first.indexed ∈
        (drawing graph).indexedSegments :=
    retainedCarrierNode_indexed_mem graph
      (retainedDrawingCompleteCarrierLinkRaw_endpoints_mem
        graph translatedLinkMember).1
  have endpointBounds :
      (drawing graph).SegmentEndpointsInExpandedSquare := by
    intro indexed indexedMember
    have bounds :=
      drawing_indexedSegment_endpoints_inExpandedDrawingSquare
        wellFormed degree isLocal indexedMember
    simpa [PeriodicGridDrawing.PositionInExpandedSquare,
      InExpandedDrawingSquare, drawing_gridSize] using bounds
  apply
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_crossover_of_contact_close
      formula wellFormed degree isLocal first second
      link firstComponentEq crossing localClauseIndex secondSourceEq
  intro meet
  have carrierContainsTranslated :
      (translatedLink.first.indexed.segment.translate
        ((drawing graph).periodTranslation
          translatedLink.first.translate)).Contains
        translatedCrossing.point := by
    simpa [translatedCrossing, CrossingRecord.periodTranslate,
      graph, anchorShift, sourceShift, translatedLink,
      CarrierNode.supportingSegment] using carrierContains meet
  have firstRelativeClose :
      Cell.sub translatedLink.first.translate
          translatedCrossing.firstTranslate ∈
        PeriodicGridDrawing.doubleNeighborTranslations := by
    exact
      PeriodicGridDrawing.relativeTranslate_isDoubleNeighbor_of_contains
        endpointBounds carrierIndexedMember
        (by
          simpa [translatedCrossing,
            CrossingRecord.periodTranslate] using crossingSound.1)
        carrierContainsTranslated
        (by
          simpa [translatedCrossing,
            CrossingRecord.periodTranslate,
            CrossingRecord.firstSegment] using
            GridSegment.contains_of_interiorContains
              firstInteriorContains)
  have secondRelativeClose :
      Cell.sub translatedLink.first.translate
          translatedCrossing.secondTranslate ∈
        PeriodicGridDrawing.doubleNeighborTranslations := by
    exact
      PeriodicGridDrawing.relativeTranslate_isDoubleNeighbor_of_contains
        endpointBounds carrierIndexedMember
        (by
          simpa [translatedCrossing,
            CrossingRecord.periodTranslate] using crossingSound.2.1)
        carrierContainsTranslated
        (by
          simpa [translatedCrossing,
            CrossingRecord.periodTranslate,
            CrossingRecord.secondSegment] using
            GridSegment.contains_of_interiorContains
              secondInteriorContains)
  have desiredEq (crossingTranslate : Cell) :
      Cell.sub
          (Cell.add
            (Cell.add link.first.translate
              (Cell.neg first.sourceClauseAnchor))
            (Cell.sub firstShift secondShift))
          (Cell.add crossingTranslate
            (Cell.neg second.sourceClauseAnchor)) =
        Cell.sub translatedLink.first.translate
          (Cell.add crossingTranslate sourceShift) := by
    have translatedLinkTranslateEq :
        translatedLink.first.translate =
          Cell.add link.first.translate anchorShift := by
      simp [translatedLink, carrierLinkPeriodTranslate_first,
        CarrierNode.translate_periodTranslate]
    rw [translatedLinkTranslateEq]
    simp only [sourceShift]
    rw [second.physicalShift_eq]
    apply Prod.ext <;>
      simp [anchorShift, Cell.sub, Cell.add, Cell.neg] <;>
      ring
  constructor
  · rw [desiredEq crossing.firstTranslate]
    simpa [translatedCrossing,
      CrossingRecord.periodTranslate] using firstRelativeClose
  · rw [desiredEq crossing.secondTranslate]
    simpa [translatedCrossing,
      CrossingRecord.periodTranslate] using secondRelativeClose

/-- Carrier--bend separation reduces to a doubled-halo bound between the
anchor-normalized carrier occurrence and the anchor-normalized bend route
occurrence. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_bend_of_contact_close
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (link : EqualityLink CarrierNode)
    (firstComponentEq :
      first.routeWitness.metadata.source.component = .carrier link)
    (routeBend : RouteBend)
    (localClauseIndex : Nat)
    (secondSourceEq :
      second.routeWitness.metadata.source =
        .bend routeBend localClauseIndex)
    (contactClose :
      GridSegment.InteriorsMeet
          (firstIndexed.segment.translate
            ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
              formula).periodTranslation firstShift))
          (secondIndexed.segment.translate
            ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
              formula).periodTranslation secondShift)) →
        Cell.sub
            (Cell.add
              (Cell.add link.first.translate
                (Cell.neg first.sourceClauseAnchor))
              (Cell.sub firstShift secondShift))
            (Cell.add routeBend.translate
              (Cell.neg second.sourceClauseAnchor)) ∈
          PeriodicGridDrawing.doubleNeighborTranslations) :
    ¬GridSegment.InteriorsMeet
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift))
      (secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)) := by
  have secondNotCarrier :
      ¬∃ secondLink,
        second.routeWitness.metadata.source.component =
          .carrier secondLink := by
    rintro ⟨secondLink, componentEq⟩
    rw [secondSourceEq] at componentEq
    simp [DrawingPlanarSATClauseSource.component] at componentEq
  apply
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_noncarrier_of_balanced_source_coordinate
      formula wellFormed degree isLocal first second
      link firstComponentEq secondNotCarrier
      (Cell.add routeBend.translate
        (Cell.neg second.sourceClauseAnchor))
  · intro adjustment adjustmentNeighbor
    rw [secondSourceEq]
    change
      IsNeighborTranslation
        (Cell.add routeBend.translate
          (Cell.add
            (Cell.neg second.sourceClauseAnchor)
            adjustment))
    simpa [Cell.add, add_assoc] using adjustmentNeighbor
  · exact contactClose

/-- Every hypothetical carrier--bend contact satisfies the doubled-halo
bound required above: both the carrier and an adjacent bend segment contain
the translated bend point. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_bend
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (link : EqualityLink CarrierNode)
    (firstComponentEq :
      first.routeWitness.metadata.source.component = .carrier link)
    (routeBend : RouteBend)
    (localClauseIndex : Nat)
    (secondSourceEq :
      second.routeWitness.metadata.source =
        .bend routeBend localClauseIndex) :
    ¬GridSegment.InteriorsMeet
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift))
      (secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)) := by
  let graph := formula.incidenceGraph
  let anchorShift := Cell.neg first.sourceClauseAnchor
  let sourceShift := Cell.sub second.physicalShift firstShift
  let translatedLink :=
    carrierLinkPeriodTranslate graph link anchorShift
  have secondNotCarrier :
      ¬∃ secondLink,
        second.routeWitness.metadata.source.component =
          .carrier secondLink := by
    rintro ⟨secondLink, componentEq⟩
    rw [secondSourceEq] at componentEq
    simp [DrawingPlanarSATClauseSource.component] at componentEq
  have routeBendMember :
      routeBend ∈ (drawingRouteBends graph).dedup := by
    have sourceMember := second.source_retainedComponentMember
    rw [secondSourceEq] at sourceMember
    exact sourceMember
  have centerEq :
      second.routeWitness.metadata.source.component.macrocellCenter
          formula =
        some (routeBend.drawingPoint graph) := by
    rw [secondSourceEq]
    rfl
  have carrierContains :=
    first.anchorNormalizedCarrier_supportingSegment_contains_translatedMacrocellCenter_of_contact
      formula wellFormed degree isLocal second
      link firstComponentEq secondNotCarrier
      (routeBend.drawingPoint graph) centerEq
  have incomingTerminalMember :=
    (drawingRouteBend_terminals_mem_drawingSegmentTerminals
      graph routeBendMember).1
  have incomingIndexedMember :
      routeBend.incomingTerminal.indexed ∈
        (drawing graph).indexedSegments :=
    (drawingSegmentTerminal_indexed_mem
      graph incomingTerminalMember).1
  have incomingAxisAligned :
      routeBend.incomingTerminal.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      routeBend.incomingTerminal.indexed incomingIndexedMember
  let translatedIncoming :=
    routeBend.incomingTerminal.periodTranslate sourceShift
  have targetPointEq :
      translatedIncoming.drawingPoint graph =
        Cell.add (routeBend.drawingPoint graph)
          ((drawing graph).periodTranslation sourceShift) := by
    simp only [translatedIncoming, SegmentTerminal.periodTranslate,
      RouteBend.incomingTerminal, SegmentTerminal.drawingPoint,
      GridSegment.translate]
    rw [periodTranslation_add]
    apply Prod.ext <;>
      simp [RouteBend.drawingPoint, Cell.add] <;>
      omega
  have translatedIncomingContains :
      (translatedIncoming.indexed.segment.translate
        ((drawing graph).periodTranslation
          translatedIncoming.translate)).Contains
        (translatedIncoming.drawingPoint graph) := by
    exact
      SegmentTerminal.segment_contains_drawingPoint_of_axisAligned
        graph translatedIncoming
        (by
          simpa [translatedIncoming,
            SegmentTerminal.periodTranslate] using
            incomingAxisAligned)
  rcases
      first.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq
          link firstComponentEq with
    ⟨firstLocalClauseIndex, firstSourceEq⟩
  have firstNonempty :
      first.routeWitness.metadata.clause.literals ≠ [] := by
    intro empty
    have literalMember := first.routeWitness.literalMember
    rw [empty] at literalMember
    simp at literalMember
  have translatedLinkMember :
      translatedLink ∈
        retainedDrawingCompleteCarrierLinksRaw graph := by
    simpa only [translatedLink, graph, anchorShift,
      FinalGaugedSegmentOccurrenceWitness.sourceClauseAnchor] using
      (first.routeWitness.metadata
        |>.carrier_anchorNormalize_mem_raw
          wellFormed degree isLocal first.metadata_retainedValid
          firstNonempty link firstLocalClauseIndex firstSourceEq)
  have carrierIndexedMember :
      translatedLink.first.indexed ∈
        (drawing graph).indexedSegments :=
    retainedCarrierNode_indexed_mem graph
      (retainedDrawingCompleteCarrierLinkRaw_endpoints_mem
        graph translatedLinkMember).1
  have endpointBounds :
      (drawing graph).SegmentEndpointsInExpandedSquare := by
    intro indexed indexedMember
    have bounds :=
      drawing_indexedSegment_endpoints_inExpandedDrawingSquare
        wellFormed degree isLocal indexedMember
    simpa [PeriodicGridDrawing.PositionInExpandedSquare,
      InExpandedDrawingSquare, drawing_gridSize] using bounds
  apply
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_bend_of_contact_close
      formula wellFormed degree isLocal first second
      link firstComponentEq routeBend localClauseIndex secondSourceEq
  intro meet
  have relativeClose :
      Cell.sub translatedLink.first.translate
          translatedIncoming.translate ∈
        PeriodicGridDrawing.doubleNeighborTranslations := by
    exact
      PeriodicGridDrawing.relativeTranslate_isDoubleNeighbor_of_contains
        endpointBounds carrierIndexedMember
        (by
          simpa [translatedIncoming,
            SegmentTerminal.periodTranslate] using
            incomingIndexedMember)
        (by
          rw [targetPointEq]
          simpa [graph, anchorShift, sourceShift, translatedLink,
            CarrierNode.supportingSegment] using carrierContains meet)
        translatedIncomingContains
  have desiredEq :
      Cell.sub
          (Cell.add
            (Cell.add link.first.translate
              (Cell.neg first.sourceClauseAnchor))
            (Cell.sub firstShift secondShift))
          (Cell.add routeBend.translate
            (Cell.neg second.sourceClauseAnchor)) =
        Cell.sub translatedLink.first.translate
          translatedIncoming.translate := by
    have translatedLinkTranslateEq :
        translatedLink.first.translate =
          Cell.add link.first.translate anchorShift := by
      simp [translatedLink, carrierLinkPeriodTranslate_first,
        CarrierNode.translate_periodTranslate]
    rw [translatedLinkTranslateEq]
    simp only [translatedIncoming, SegmentTerminal.periodTranslate]
    simp only [sourceShift]
    rw [second.physicalShift_eq]
    apply Prod.ext <;>
      simp [RouteBend.incomingTerminal, anchorShift,
        Cell.sub, Cell.add, Cell.neg] <;>
      ring
  rw [desiredEq]
  exact relativeClose

/-- Carrier--routed-variable separation has the same one-coordinate
reduction, using any route occurrence that represents the selected arm.
The orbit-condition bridge above permits the arm's finite presentation index
to change after balancing. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_routedVariable_of_contact_close
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (carrierLink : EqualityLink CarrierNode)
    (firstComponentEq :
      first.routeWitness.metadata.source.component =
        .carrier carrierLink)
    (site : VariableRouteSite Variable)
    (armIndex : Nat)
    (arm : DuplicatorArm)
    (routedLink : EqualityLink (PlanarSATNode Variable))
    (localClauseIndex : Nat)
    (secondSourceEq :
      second.routeWitness.metadata.source =
        .routedVariable site armIndex arm routedLink
          localClauseIndex)
    (occurrence : CNFRouteOccurrence Variable)
    (occurrenceMember :
      occurrence ∈ variableRouteOccurrencesAt formula site)
    (linkFirstEq :
      routedLink.first =
        .carrier (.terminal
          (occurrence.targetTerminal formula)))
    (contactClose :
      GridSegment.InteriorsMeet
          (firstIndexed.segment.translate
            ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
              formula).periodTranslation firstShift))
          (secondIndexed.segment.translate
            ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
              formula).periodTranslation secondShift)) →
        Cell.sub
            (Cell.add
              (Cell.add carrierLink.first.translate
                (Cell.neg first.sourceClauseAnchor))
              (Cell.sub firstShift secondShift))
            (Cell.add occurrence.translate
              (Cell.neg second.sourceClauseAnchor)) ∈
          PeriodicGridDrawing.doubleNeighborTranslations) :
    ¬GridSegment.InteriorsMeet
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift))
      (secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)) := by
  have secondNotCarrier :
      ¬∃ secondLink,
        second.routeWitness.metadata.source.component =
          .carrier secondLink := by
    rintro ⟨secondLink, componentEq⟩
    rw [secondSourceEq] at componentEq
    simp [DrawingPlanarSATClauseSource.component] at componentEq
  apply
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_noncarrier_of_balanced_source_coordinate
      formula wellFormed degree isLocal first second
      carrierLink firstComponentEq secondNotCarrier
      (Cell.add occurrence.translate
        (Cell.neg second.sourceClauseAnchor))
  · intro adjustment adjustmentNeighbor
    rw [secondSourceEq]
    refine ⟨occurrence, occurrenceMember, linkFirstEq, ?_⟩
    simpa [Cell.add, add_assoc] using adjustmentNeighbor
  · exact contactClose

/-- Final carrier segments have disjoint interiors from every represented
routed-variable arm occurrence at arbitrary quotient translates. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_routedVariable
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (carrierLink : EqualityLink CarrierNode)
    (firstComponentEq :
      first.routeWitness.metadata.source.component =
        .carrier carrierLink)
    (site : VariableRouteSite Variable)
    (armIndex : Nat)
    (arm : DuplicatorArm)
    (routedLink : EqualityLink (PlanarSATNode Variable))
    (localClauseIndex : Nat)
    (secondSourceEq :
      second.routeWitness.metadata.source =
        .routedVariable site armIndex arm routedLink
          localClauseIndex)
    (occurrence : CNFRouteOccurrence Variable)
    (occurrenceMember :
      occurrence ∈ variableRouteOccurrencesAt formula site)
    (linkFirstEq :
      routedLink.first =
        .carrier (.terminal
          (occurrence.targetTerminal formula))) :
    ¬GridSegment.InteriorsMeet
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift))
      (secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)) := by
  have secondNotCarrier :
      ¬∃ secondLink,
        second.routeWitness.metadata.source.component =
          .carrier secondLink := by
    rintro ⟨secondLink, componentEq⟩
    rw [secondSourceEq] at componentEq
    simp [DrawingPlanarSATClauseSource.component] at componentEq
  have sourceMember := second.source_retainedComponentMember
  rw [secondSourceEq] at sourceMember
  have siteMember :
      site ∈ drawingVariableRouteSites formula :=
    sourceMember.1
  have centerEq :
      second.routeWitness.metadata.source.component.macrocellCenter
          formula =
        some
          (liftedIncidenceVertexPosition
            formula (.variable site.1) site.2) := by
    rw [secondSourceEq]
    rfl
  have occurrenceData :=
    variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
      formula site occurrenceMember
  have siteTranslateEq :
      Cell.add occurrence.translate occurrence.edge.offset =
        site.2 :=
    congrArg Prod.snd occurrenceData.2
  have edgeMember :=
    occurrence.taggedEdge_mem formula occurrenceData.1
  have edgeLocal : occurrence.edge.span ≤ 1 :=
    isLocal occurrence.edge
      (List.fst_mem_of_mem_zipIdx edgeMember)
  have offsetNeighbor :
      IsNeighborTranslation occurrence.edge.offset :=
    PeriodicEdge.offset_neighbor_of_local
      occurrence.edge edgeLocal
  apply
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_routedVariable_of_contact_close
      formula wellFormed degree isLocal first second
      carrierLink firstComponentEq
      site armIndex arm routedLink localClauseIndex
      secondSourceEq occurrence occurrenceMember linkFirstEq
  intro meet
  have relativeSiteNeighbor :=
    first.carrier_liftedVertex_relative_neighbor_of_contact
      formula wellFormed degree isLocal second
      carrierLink firstComponentEq secondNotCarrier
      (.variable site.1)
      (drawingVariableRouteSite_vertex_mem formula siteMember)
      site.2 centerEq meet
  have sumMember :=
    relativeSiteNeighbor.add_mem_doubleNeighborTranslations
      offsetNeighbor
  have desiredEq :
      Cell.sub
          (Cell.add
            (Cell.add carrierLink.first.translate
              (Cell.neg first.sourceClauseAnchor))
            (Cell.sub firstShift secondShift))
          (Cell.add occurrence.translate
            (Cell.neg second.sourceClauseAnchor)) =
        Cell.add
          (Cell.sub
            (Cell.add carrierLink.first.translate
              (Cell.neg first.sourceClauseAnchor))
            (Cell.add site.2
              (Cell.sub second.physicalShift firstShift)))
          occurrence.edge.offset := by
    rw [second.physicalShift_eq, ← siteTranslateEq]
    rcases firstShift with ⟨firstShiftX, firstShiftY⟩
    rcases secondShift with ⟨secondShiftX, secondShiftY⟩
    rcases first.sourceClauseAnchor with
      ⟨firstAnchorX, firstAnchorY⟩
    rcases second.sourceClauseAnchor with
      ⟨secondAnchorX, secondAnchorY⟩
    rcases occurrence.translate with
      ⟨occurrenceX, occurrenceY⟩
    rcases occurrence.edge.offset with
      ⟨offsetX, offsetY⟩
    apply Prod.ext <;>
      simp [Cell.sub, Cell.add, Cell.neg] <;>
      ring
  rw [desiredEq]
  exact sumMember

/-- If a hypothetical final carrier--noncarrier contact keeps the physically
aligned noncarrier source in the retained halo, finite raw-carrier planarity
already gives a contradiction. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_noncarrier_of_contact_retained
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (link : EqualityLink CarrierNode)
    (firstComponentEq :
      first.routeWitness.metadata.source.component = .carrier link)
    (secondNotCarrier :
      ¬∃ secondLink,
        second.routeWitness.metadata.source.component =
          .carrier secondLink)
    (contactRetained :
      GridSegment.InteriorsMeet
          (firstIndexed.segment.translate
            ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
              formula).periodTranslation firstShift))
          (secondIndexed.segment.translate
            ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
              formula).periodTranslation secondShift)) →
        (second.routeWitness.metadata.source.periodTranslate formula
          (Cell.sub second.physicalShift first.physicalShift)
            |>.RetainedComponentMember formula)) :
    ¬GridSegment.InteriorsMeet
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift))
      (secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)) := by
  intro meet
  have carrierData :=
    first.carrier_source_raw_and_neighbor link firstComponentEq
  have commonShiftEq :
      Cell.sub first.physicalShift (0, 0) =
        Cell.sub second.physicalShift
          (Cell.sub second.physicalShift first.physicalShift) := by
    rcases first.physicalShift with ⟨firstX, firstY⟩
    rcases second.physicalShift with ⟨secondX, secondY⟩
    simp only [Cell.sub, Prod.mk.injEq]
    constructor <;> ring
  have translatedLinkEq :
      carrierLinkPeriodTranslate formula.incidenceGraph link (0, 0) =
        link := by
    rcases link with ⟨firstNode, secondNode, positions⟩
    rcases firstNode with firstBoundary | firstTerminal <;>
      rcases secondNode with secondBoundary | secondTerminal <;>
      simp [carrierLinkPeriodTranslate,
        CarrierNode.periodTranslate,
        SegmentTerminal.periodTranslate,
        CrossingBoundary.periodTranslate,
        CrossingRecord.periodTranslate,
        EqualityPositions.periodTranslate,
        carrierMacroPeriodTranslation,
        PeriodicGridDrawing.periodTranslation,
        Cell.add, Cell.scale]
  exact
    (retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_noncarrier_of_common_raw
      formula wellFormed degree isLocal first second
      (0, 0) (Cell.sub second.physicalShift first.physicalShift)
      commonShiftEq link firstComponentEq secondNotCarrier
      (by simpa only [translatedLinkEq] using carrierData.1)
      (by simpa using carrierData.2)
      (contactRetained meet))
      meet

/-- Equivalently, any hypothetical contact would force the physically aligned
noncarrier source outside the retained halo.  Later family-specific geometry
will contradict this escape conclusion. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_translated_noncarrier_not_retained_of_carrier_contact
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (link : EqualityLink CarrierNode)
    (firstComponentEq :
      first.routeWitness.metadata.source.component = .carrier link)
    (secondNotCarrier :
      ¬∃ secondLink,
        second.routeWitness.metadata.source.component =
          .carrier secondLink)
    (meet :
      GridSegment.InteriorsMeet
        (firstIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation firstShift))
        (secondIndexed.segment.translate
          ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).periodTranslation secondShift))) :
    ¬((second.routeWitness.metadata.source.periodTranslate formula
        (Cell.sub second.physicalShift first.physicalShift))
          |>.RetainedComponentMember formula) := by
  intro translatedMember
  exact
    (retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carrier_noncarrier_of_contact_retained
      formula wellFormed degree isLocal first second link
      firstComponentEq secondNotCarrier
      (fun _ => translatedMember))
      meet

end PeriodicOrthocrossing
end LeanTrominoes
