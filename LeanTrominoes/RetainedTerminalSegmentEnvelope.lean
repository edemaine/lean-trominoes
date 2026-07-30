import LeanTrominoes.RectangleLineEnvelope
import LeanTrominoes.RetainedAngularFanSourceMixedSeparation

/-!
# Closed envelopes of retained terminal segments

For a classified retained terminal, the selected transverse functional
annihilates its primitive direction.  Hence the discarded final segment
lies on exactly the supporting line used by the mixed outer-corridor
certificate.

The final theorem restates `SourcePrefixCorridorSeparated` as a finite,
decidable absence of point contacts and axis-segment contacts with this
closed terminal envelope.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

/-- Both endpoints of a classified final terminal segment have the same
value under its selected transverse functional. -/
theorem retainedTerminalFinalSegment_linearValue_eq
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal) :
    Cell.linearValue
        (retainedTerminalFanOuterTransverseNormal terminal.1)
        (polylineLastEntrance route) =
      Cell.linearValue
        (retainedTerminalFanOuterTransverseNormal terminal.1)
        (route.getLastD (0, 0)) := by
  rw [polylineLastEntrance_eq_retainedTerminalSplicePoint
    routeLength classified]
  rcases terminal with ⟨direction, length⟩
  have annihilates :=
    retainedTerminalFanOuterTransverseNormal_primitive_zero direction
  simp only [retainedTerminalSplicePoint,
    Cell.linearValue_add, Cell.linearValue_scale,
    annihilates, mul_zero, add_zero]

/-- A point contact with the closed envelope of a discarded classified
terminal segment. -/
def PointMeetsRetainedTerminalSegmentEnvelope
    (point : Cell)
    (referenceRoute : List Cell)
    (referenceDirection : RetainedTerminalDirection) : Prop :=
  let referenceSegment : GridSegment :=
    ⟨polylineLastEntrance referenceRoute,
      referenceRoute.getLastD (0, 0)⟩
  referenceSegment.PointInLinearEnvelope
    (retainedTerminalFanOuterTransverseNormal referenceDirection)
    point

instance
    (point : Cell)
    (referenceRoute : List Cell)
    (referenceDirection : RetainedTerminalDirection) :
    Decidable
      (PointMeetsRetainedTerminalSegmentEnvelope
        point referenceRoute referenceDirection) := by
  unfold PointMeetsRetainedTerminalSegmentEnvelope
  infer_instance

/-- An axis-aligned segment contact with the closed envelope of a discarded
classified terminal segment. -/
def AxisSegmentMeetsRetainedTerminalSegmentEnvelope
    (segment : GridSegment)
    (referenceRoute : List Cell)
    (referenceDirection : RetainedTerminalDirection) : Prop :=
  let referenceSegment : GridSegment :=
    ⟨polylineLastEntrance referenceRoute,
      referenceRoute.getLastD (0, 0)⟩
  segment.AxisSegmentMeetsLinearEnvelope
    referenceSegment
    (retainedTerminalFanOuterTransverseNormal referenceDirection)

instance
    (segment : GridSegment)
    (referenceRoute : List Cell)
    (referenceDirection : RetainedTerminalDirection) :
    Decidable
      (AxisSegmentMeetsRetainedTerminalSegmentEnvelope
        segment referenceRoute referenceDirection) := by
  unfold AxisSegmentMeetsRetainedTerminalSegmentEnvelope
  infer_instance

/-- The discarded final segment's splice endpoint belongs to the precise
closed envelope used by its mixed corridor certificate. -/
theorem retainedTerminalFinalSegment_start_meets_envelope
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal) :
    PointMeetsRetainedTerminalSegmentEnvelope
      (polylineLastEntrance route) route terminal.1 := by
  unfold PointMeetsRetainedTerminalSegmentEnvelope
  apply GridSegment.start_pointInLinearEnvelope
  exact retainedTerminalFinalSegment_linearValue_eq
    route terminal routeLength classified

/-- The discarded final segment's variable endpoint also belongs to its
closed terminal envelope. -/
theorem retainedTerminalFinalSegment_finish_meets_envelope
    (route : List Cell)
    (terminal : RetainedTerminalData) :
    PointMeetsRetainedTerminalSegmentEnvelope
      (route.getLastD (0, 0)) route terminal.1 := by
  exact GridSegment.finish_pointInLinearEnvelope _ _

/-- The mixed source-prefix corridor certificate is exactly the finite
absence of point and axis-segment contacts with the retained terminal
envelope. -/
theorem sourcePrefixCorridorSeparated_iff_no_terminalEnvelopeContacts
    (sourceRoute referenceRoute : List Cell)
    (referenceDirection : RetainedTerminalDirection) :
    SourcePrefixCorridorSeparated
        sourceRoute referenceRoute referenceDirection ↔
      (∀ point ∈ sourceRoute.dropLast,
          ¬PointMeetsRetainedTerminalSegmentEnvelope
            point referenceRoute referenceDirection) ∧
        ∀ segment ∈ gridPolylineSegments sourceRoute.dropLast,
          segment.IsAxisAligned →
            ¬AxisSegmentMeetsRetainedTerminalSegmentEnvelope
              segment referenceRoute referenceDirection := by
  let referenceSegment : GridSegment :=
    ⟨polylineLastEntrance referenceRoute,
      referenceRoute.getLastD (0, 0)⟩
  let normal :=
    retainedTerminalFanOuterTransverseNormal referenceDirection
  change
    ((∀ point ∈ sourceRoute.dropLast,
        PointSeparatesRectangleOrLine
          point
          referenceSegment.coordinateLower
          referenceSegment.coordinateUpper
          referenceSegment.finish normal) ∧
      (∀ segment ∈ gridPolylineSegments sourceRoute.dropLast,
        segment.IsAxisAligned →
          SegmentSeparatesRectangleOrLine
            segment
            referenceSegment.coordinateLower
            referenceSegment.coordinateUpper
            referenceSegment.finish normal)) ↔
      (∀ point ∈ sourceRoute.dropLast,
        ¬referenceSegment.PointInLinearEnvelope normal point) ∧
      (∀ segment ∈ gridPolylineSegments sourceRoute.dropLast,
        segment.IsAxisAligned →
          ¬segment.AxisSegmentMeetsLinearEnvelope
            referenceSegment normal)
  constructor
  · rintro ⟨points, segments⟩
    constructor
    · intro point pointMember
      exact
        (pointSeparatesRectangleOrLine_iff_not_pointInLinearEnvelope
          point referenceSegment normal).mp
          (points point pointMember)
    · intro segment segmentMember aligned
      exact
        (segmentSeparatesRectangleOrLine_iff_not_axisSegmentMeetsLinearEnvelope
          segment referenceSegment normal aligned).mp
          (segments segment segmentMember aligned)
  · rintro ⟨points, segments⟩
    constructor
    · intro point pointMember
      exact
        (pointSeparatesRectangleOrLine_iff_not_pointInLinearEnvelope
          point referenceSegment normal).mpr
          (points point pointMember)
    · intro segment segmentMember aligned
      exact
        (segmentSeparatesRectangleOrLine_iff_not_axisSegmentMeetsLinearEnvelope
          segment referenceSegment normal aligned).mpr
          (segments segment segmentMember aligned)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
