import LeanTrominoes.RetainedTerminalSegmentEnvelope

/-!
# Integral checkpoints for retained terminal envelopes

The total fan refinement is `288`, divisible by every nonunit coordinate
appearing in the eleven retained terminal primitives.  Consequently a
lattice contact with a terminal segment's exact rectangle-and-line envelope
becomes an actual integral checkpoint on the refined terminal segment.

This turns the new diagonal contact predicate into ordinary scaled
point/axis-segment containment, which is the form needed by the finite
component geometry.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- A point is one of the primitive checkpoints between the refined
variable endpoint and the refined discarded splice endpoint. -/
def IsRetainedTerminalRefinedCheckpoint
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (point : Cell) : Prop :=
  ∃ index : Nat,
    index ≤ retainedTerminalFanTotalRefinement * terminal.2 ∧
      point =
        Cell.add
          (Cell.scale retainedTerminalFanTotalRefinement
            (route.getLastD (0, 0)))
          (Cell.scale index terminal.1.primitive)

instance
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (point : Cell) :
    Decidable
      (IsRetainedTerminalRefinedCheckpoint route terminal point) := by
  unfold IsRetainedTerminalRefinedCheckpoint
  infer_instance

/-- A refined axis-aligned segment contains a primitive checkpoint of the
discarded retained terminal segment. -/
def AxisSegmentContainsRetainedTerminalRefinedCheckpoint
    (source : GridSegment)
    (route : List Cell)
    (terminal : RetainedTerminalData) : Prop :=
  ∃ index : Nat,
    index ≤ retainedTerminalFanTotalRefinement * terminal.2 ∧
      (source.scale retainedTerminalFanTotalRefinement).Contains
        (Cell.add
          (Cell.scale retainedTerminalFanTotalRefinement
            (route.getLastD (0, 0)))
          (Cell.scale index terminal.1.primitive))

instance
    (source : GridSegment)
    (route : List Cell)
    (terminal : RetainedTerminalData) :
    Decidable
      (AxisSegmentContainsRetainedTerminalRefinedCheckpoint
        source route terminal) := by
  unfold AxisSegmentContainsRetainedTerminalRefinedCheckpoint
  infer_instance

local macro "solve_terminal_checkpoint" contact:ident : tactic =>
  `(tactic|
    (simp [retainedTerminalFanTotalRefinement_eq,
        retainedTerminalFanOuterTransverseNormal,
        RetainedTerminalDirection.primitive,
        OccurrenceSplitRing.Port.unitVector,
        routedClauseRayPrimitive,
        InClosedGridRectangle,
        GridSegment.coordinateLower,
        GridSegment.coordinateUpper,
        Cell.linearValue, Cell.add, Cell.sub, Cell.scale,
        min_def, max_def] at $contact ⊢ <;>
      omega))

local macro "solve_terminal_axis_checkpoint" : tactic =>
  `(tactic|
    simp only [ClosedGridRectanglesSeparated] at * <;>
    push Not at * <;>
    simp_all [retainedTerminalFanTotalRefinement_eq,
        retainedTerminalFanOuterTransverseNormal,
        RetainedTerminalDirection.primitive,
        OccurrenceSplitRing.Port.unitVector,
        routedClauseRayPrimitive,
        InClosedGridRectangle,
        ClosedGridRectanglesSeparated,
        GridSegment.coordinateLower,
        GridSegment.coordinateUpper,
        GridSegment.scale,
        GridSegment.Contains,
        GridSegment.IsHorizontal,
        GridSegment.IsVertical,
        GridSegment.Between,
        Cell.linearValue, Cell.add, Cell.sub, Cell.scale,
        min_def, max_def] <;>
      (try split_ifs at *) <;>
      omega)

/-- An integer checkpoint parameter in the closed refined range can be
converted to the natural parameter used by the executable checkpoint
predicate. -/
theorem isRetainedTerminalRefinedCheckpoint_of_exists_int
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (point : Cell)
    (witness :
      ∃ index : Int,
        0 ≤ index ∧
          index ≤
            retainedTerminalFanTotalRefinement * (terminal.2 : Int) ∧
          point =
            Cell.add
              (Cell.scale retainedTerminalFanTotalRefinement
                (route.getLastD (0, 0)))
              (Cell.scale index terminal.1.primitive)) :
    IsRetainedTerminalRefinedCheckpoint route terminal point := by
  rcases witness with ⟨index, indexNonnegative, indexBound, pointEq⟩
  refine ⟨index.toNat, ?_, ?_⟩
  · have castIndex :
        (index.toNat : Int) = index :=
      Int.toNat_of_nonneg indexNonnegative
    omega
  · simpa [Int.toNat_of_nonneg indexNonnegative] using pointEq

/-- An integer checkpoint parameter in the closed refined range can be
converted to the natural parameter used by segment containment. -/
theorem
    axisSegmentContainsRetainedTerminalRefinedCheckpoint_of_exists_int
    (source : GridSegment)
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (witness :
      ∃ index : Int,
        0 ≤ index ∧
          index ≤
            retainedTerminalFanTotalRefinement * (terminal.2 : Int) ∧
          (source.scale retainedTerminalFanTotalRefinement).Contains
            (Cell.add
              (Cell.scale retainedTerminalFanTotalRefinement
                (route.getLastD (0, 0)))
              (Cell.scale index terminal.1.primitive))) :
    AxisSegmentContainsRetainedTerminalRefinedCheckpoint
      source route terminal := by
  rcases witness with
    ⟨index, indexNonnegative, indexBound, contains⟩
  refine ⟨index.toNat, ?_, ?_⟩
  · have castIndex :
        (index.toNat : Int) = index :=
      Int.toNat_of_nonneg indexNonnegative
    omega
  · simpa [Int.toNat_of_nonneg indexNonnegative] using contains

/-- Every lattice point in a classified terminal envelope scales to an
actual primitive checkpoint on the refined discarded segment. -/
theorem pointMeetsRetainedTerminalSegmentEnvelope_scale_isCheckpoint
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (point : Cell)
    (contact :
      PointMeetsRetainedTerminalSegmentEnvelope
        point route terminal.1) :
    IsRetainedTerminalRefinedCheckpoint
      route terminal
      (Cell.scale retainedTerminalFanTotalRefinement point) := by
  have startEq :=
    polylineLastEntrance_eq_retainedTerminalSplicePoint
      routeLength classified
  unfold PointMeetsRetainedTerminalSegmentEnvelope
    GridSegment.PointInLinearEnvelope at contact
  apply isRetainedTerminalRefinedCheckpoint_of_exists_int
  generalize centerEq :
      route.getLastD (0, 0) = center at startEq contact ⊢
  rcases center with ⟨centerX, centerY⟩
  rcases point with ⟨pointX, pointY⟩
  rcases terminal with ⟨direction, length⟩
  simp only [startEq, retainedTerminalSplicePoint] at contact
  cases direction with
  | compass port =>
      cases port
      case northwest =>
        refine ⟨288 * (centerX - pointX), ?_, ?_, ?_⟩ <;>
          solve_terminal_checkpoint contact
      case north =>
        refine ⟨288 * (centerY - pointY), ?_, ?_, ?_⟩ <;>
          solve_terminal_checkpoint contact
      case northeast =>
        refine ⟨288 * (pointX - centerX), ?_, ?_, ?_⟩ <;>
          solve_terminal_checkpoint contact
      case east =>
        refine ⟨288 * (pointX - centerX), ?_, ?_, ?_⟩ <;>
          solve_terminal_checkpoint contact
      case southeast =>
        refine ⟨288 * (pointX - centerX), ?_, ?_, ?_⟩ <;>
          solve_terminal_checkpoint contact
      case south =>
        refine ⟨288 * (pointY - centerY), ?_, ?_, ?_⟩ <;>
          solve_terminal_checkpoint contact
      case southwest =>
        refine ⟨288 * (centerX - pointX), ?_, ?_, ?_⟩ <;>
          solve_terminal_checkpoint contact
      case west =>
        refine ⟨288 * (centerX - pointX), ?_, ?_, ?_⟩ <;>
          solve_terminal_checkpoint contact
  | routedClause arm =>
      cases arm
      case left =>
        refine ⟨32 * (pointX - centerX), ?_, ?_, ?_⟩ <;>
          solve_terminal_checkpoint contact
      case middle =>
        refine ⟨72 * (pointX - centerX), ?_, ?_, ?_⟩ <;>
          solve_terminal_checkpoint contact
      case right =>
        refine ⟨288 * (centerX - pointX), ?_, ?_, ?_⟩ <;>
          solve_terminal_checkpoint contact

set_option maxHeartbeats 800000

/-- Every classified terminal-envelope contact by an axis-aligned segment
contains an exact primitive checkpoint after the common refinement. -/
theorem
    axisSegmentMeetsRetainedTerminalSegmentEnvelope_scale_containsCheckpoint
    (source : GridSegment)
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (contact :
      AxisSegmentMeetsRetainedTerminalSegmentEnvelope
        source route terminal.1) :
    AxisSegmentContainsRetainedTerminalRefinedCheckpoint
      source route terminal := by
  have startEq :=
    polylineLastEntrance_eq_retainedTerminalSplicePoint
      routeLength classified
  unfold AxisSegmentMeetsRetainedTerminalSegmentEnvelope
    GridSegment.AxisSegmentMeetsLinearEnvelope at contact
  apply
    axisSegmentContainsRetainedTerminalRefinedCheckpoint_of_exists_int
  generalize centerEq :
      route.getLastD (0, 0) = center at startEq contact ⊢
  rcases center with ⟨centerX, centerY⟩
  rcases source with
    ⟨⟨sourceStartX, sourceStartY⟩,
      ⟨sourceFinishX, sourceFinishY⟩⟩
  rcases terminal with ⟨direction, length⟩
  simp only [startEq, retainedTerminalSplicePoint] at contact
  rcases contact with
    ⟨aligned, rectanglesMeet, bracketed⟩
  cases direction with
  | compass port =>
      cases port <;>
        rcases aligned with horizontal | vertical
      case northwest.inl =>
        refine ⟨288 * (centerY - sourceStartY), ?_, ?_, ?_⟩ <;>
          solve_terminal_axis_checkpoint
      case northwest.inr =>
        refine ⟨288 * (centerX - sourceStartX), ?_, ?_, ?_⟩ <;>
          solve_terminal_axis_checkpoint
      case north.inl =>
        refine ⟨288 * (centerY - sourceStartY), ?_, ?_, ?_⟩ <;>
          solve_terminal_axis_checkpoint
      case north.inr =>
        let pointY :=
          max (min sourceStartY sourceFinishY)
            (centerY - length)
        refine ⟨288 * (centerY - pointY), ?_, ?_, ?_⟩ <;>
          solve_terminal_axis_checkpoint
      case northeast.inl =>
        refine ⟨288 * (centerY - sourceStartY), ?_, ?_, ?_⟩ <;>
          solve_terminal_axis_checkpoint
      case northeast.inr =>
        refine ⟨288 * (sourceStartX - centerX), ?_, ?_, ?_⟩ <;>
          solve_terminal_axis_checkpoint
      case east.inl =>
        let pointX :=
          max (min sourceStartX sourceFinishX) centerX
        refine ⟨288 * (pointX - centerX), ?_, ?_, ?_⟩ <;>
          solve_terminal_axis_checkpoint
      case east.inr =>
        refine ⟨288 * (sourceStartX - centerX), ?_, ?_, ?_⟩ <;>
          solve_terminal_axis_checkpoint
      case southeast.inl =>
        refine ⟨288 * (sourceStartY - centerY), ?_, ?_, ?_⟩ <;>
          solve_terminal_axis_checkpoint
      case southeast.inr =>
        refine ⟨288 * (sourceStartX - centerX), ?_, ?_, ?_⟩ <;>
          solve_terminal_axis_checkpoint
      case south.inl =>
        refine ⟨288 * (sourceStartY - centerY), ?_, ?_, ?_⟩ <;>
          solve_terminal_axis_checkpoint
      case south.inr =>
        let pointY :=
          max (min sourceStartY sourceFinishY) centerY
        refine ⟨288 * (pointY - centerY), ?_, ?_, ?_⟩ <;>
          solve_terminal_axis_checkpoint
      case southwest.inl =>
        refine ⟨288 * (sourceStartY - centerY), ?_, ?_, ?_⟩ <;>
          solve_terminal_axis_checkpoint
      case southwest.inr =>
        refine ⟨288 * (centerX - sourceStartX), ?_, ?_, ?_⟩ <;>
          solve_terminal_axis_checkpoint
      case west.inl =>
        let pointX :=
          max (min sourceStartX sourceFinishX)
            (centerX - length)
        refine ⟨288 * (centerX - pointX), ?_, ?_, ?_⟩ <;>
          solve_terminal_axis_checkpoint
      case west.inr =>
        refine ⟨288 * (centerX - sourceStartX), ?_, ?_, ?_⟩ <;>
          solve_terminal_axis_checkpoint
  | routedClause arm =>
      cases arm <;>
        rcases aligned with horizontal | vertical
      case left.inl =>
        refine ⟨72 * (sourceStartY - centerY), ?_, ?_, ?_⟩ <;>
          solve_terminal_axis_checkpoint
      case left.inr =>
        refine ⟨32 * (sourceStartX - centerX), ?_, ?_, ?_⟩ <;>
          solve_terminal_axis_checkpoint
      case middle.inl =>
        refine ⟨288 * (centerY - sourceStartY), ?_, ?_, ?_⟩ <;>
          solve_terminal_axis_checkpoint
      case middle.inr =>
        refine ⟨72 * (sourceStartX - centerX), ?_, ?_, ?_⟩ <;>
          solve_terminal_axis_checkpoint
      case right.inl =>
        refine ⟨72 * (sourceStartY - centerY), ?_, ?_, ?_⟩ <;>
          solve_terminal_axis_checkpoint
      case right.inr =>
        refine ⟨288 * (centerX - sourceStartX), ?_, ?_, ?_⟩ <;>
          solve_terminal_axis_checkpoint

/-- A finite source-prefix certificate saying that no scaled source vertex
or source segment reaches a primitive checkpoint of the discarded retained
terminal. -/
def SourcePrefixAvoidsRetainedTerminalRefinedCheckpoints
    (sourceRoute referenceRoute : List Cell)
    (referenceTerminal : RetainedTerminalData) : Prop :=
  (∀ point ∈ sourceRoute.dropLast,
      ¬IsRetainedTerminalRefinedCheckpoint
        referenceRoute referenceTerminal
        (Cell.scale retainedTerminalFanTotalRefinement point)) ∧
    ∀ segment ∈ gridPolylineSegments sourceRoute.dropLast,
      ¬AxisSegmentContainsRetainedTerminalRefinedCheckpoint
        segment referenceRoute referenceTerminal

instance
    (sourceRoute referenceRoute : List Cell)
    (referenceTerminal : RetainedTerminalData) :
    Decidable
      (SourcePrefixAvoidsRetainedTerminalRefinedCheckpoints
        sourceRoute referenceRoute referenceTerminal) := by
  unfold SourcePrefixAvoidsRetainedTerminalRefinedCheckpoints
  infer_instance

/-- Avoiding all refined primitive checkpoints is sufficient for the mixed
source-prefix corridor certificate used by the outer angular fan. -/
theorem sourcePrefixCorridorSeparated_of_avoids_refinedCheckpoints
    (sourceRoute referenceRoute : List Cell)
    (referenceTerminal : RetainedTerminalData)
    (referenceLength : 2 ≤ referenceRoute.length)
    (referenceClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector referenceRoute) =
        some referenceTerminal)
    (avoids :
      SourcePrefixAvoidsRetainedTerminalRefinedCheckpoints
        sourceRoute referenceRoute referenceTerminal) :
    SourcePrefixCorridorSeparated
      sourceRoute referenceRoute referenceTerminal.1 := by
  apply
    (sourcePrefixCorridorSeparated_iff_no_terminalEnvelopeContacts
      sourceRoute referenceRoute referenceTerminal.1).mpr
  rcases avoids with ⟨pointAvoids, segmentAvoids⟩
  constructor
  · intro point pointMember contact
    exact
      pointAvoids point pointMember
        (pointMeetsRetainedTerminalSegmentEnvelope_scale_isCheckpoint
          referenceRoute referenceTerminal referenceLength
          referenceClassified point contact)
  · intro segment segmentMember _aligned contact
    exact
      segmentAvoids segment segmentMember
        (axisSegmentMeetsRetainedTerminalSegmentEnvelope_scale_containsCheckpoint
          segment referenceRoute referenceTerminal referenceLength
          referenceClassified contact)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
