import LeanTrominoes.RetainedAngularFanDirectSourceFallbackCompleteSeparation
import LeanTrominoes.RetainedRayRasterizationTranslation

/-!
# Translation covariance of complete outer fan routes

All ordinary and delayed-lane outer-fan constructions depend on their center
only through point translation.  This module records that covariance at the
radial, local, and complete-route levels so local separation certificates can
be positioned directly in the final drawing.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

/-- Translating the variable center translates the exact source gate. -/
theorem retainedAngularFanOuterDemand_gate_add
    (offset center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    (retainedAngularFanOuterDemand
      (Cell.add offset center) terminal slot).gate =
      Cell.add offset
        (retainedAngularFanOuterDemand center terminal slot).gate := by
  rcases offset with ⟨offsetX, offsetY⟩
  rcases center with ⟨centerX, centerY⟩
  simp [retainedAngularFanOuterDemand,
    retainedTerminalSplicePoint, Cell.add, Cell.scale]
  constructor <;> ring

/-- Translating a positioned lane shift translates its base gate. -/
theorem retainedTerminalFanOuterLaneShiftRouteAt_translatePolyline
    (offset gate : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    translatePolyline offset
        (retainedTerminalFanOuterLaneShiftRouteAt
          gate direction slot) =
      retainedTerminalFanOuterLaneShiftRouteAt
        (Cell.add offset gate) direction slot := by
  unfold retainedTerminalFanOuterLaneShiftRouteAt
  rw [translatePolyline_add]
  congr 1
  rcases offset with ⟨offsetX, offsetY⟩
  rcases gate with ⟨gateX, gateY⟩
  simp [Cell.add, add_comm]

/-- Translating a positioned local fan route translates its center. -/
theorem retainedTerminalFanOuterLocalRouteAt_translatePolyline
    (offset center : Cell)
    (direction : RetainedTerminalDirection)
    (slot : RetainedTerminalSlot) :
    translatePolyline offset
        (retainedTerminalFanOuterLocalRouteAt
          center direction slot) =
      retainedTerminalFanOuterLocalRouteAt
        (Cell.add offset center) direction slot := by
  unfold translatePolyline retainedTerminalFanOuterLocalRouteAt
  rw [List.map_map]
  apply List.map_congr_left
  intro point _pointMember
  rcases offset with ⟨offsetX, offsetY⟩
  rcases center with ⟨centerX, centerY⟩
  rcases point with ⟨pointX, pointY⟩
  simp [Cell.add, add_assoc]

/-- Translating the variable center translates the delayed lane-shift
checkpoint. -/
theorem retainedTerminalFanOuterSourceEscapePoint_add
    (offset center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    retainedTerminalFanOuterSourceEscapePoint
        (Cell.add offset center) terminal slot =
      Cell.add offset
        (retainedTerminalFanOuterSourceEscapePoint
          center terminal slot) := by
  unfold retainedTerminalFanOuterSourceEscapePoint
  rw [retainedAngularFanOuterDemand_gate_add]
  rcases offset with ⟨offsetX, offsetY⟩
  rcases
      (retainedAngularFanOuterDemand center terminal slot).gate with
    ⟨gateX, gateY⟩
  rcases (retainedTerminalFanOuterSourceEscapeRay terminal).vector with
    ⟨vectorX, vectorY⟩
  simp [Cell.add, add_assoc]

/-- Ordinary radial outer routes commute with translation of their center. -/
theorem retainedTerminalFanOuterRadialRoute_translatePolyline
    (offset center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    translatePolyline offset
        (retainedTerminalFanOuterRadialRoute center terminal slot) =
      retainedTerminalFanOuterRadialRoute
        (Cell.add offset center) terminal slot := by
  unfold retainedTerminalFanOuterRadialRoute
  dsimp only
  rw [translatePolyline_joinAtEndpoint,
    retainedTerminalFanOuterLaneShiftRouteAt_translatePolyline,
    RetainedRay.rasterize_translatePolyline,
    retainedAngularFanOuterDemand_gate_add]
  congr 2
  rcases offset with ⟨offsetX, offsetY⟩
  rcases
      (retainedAngularFanOuterDemand center terminal slot).gate with
    ⟨gateX, gateY⟩
  rcases retainedTerminalFanOuterLaneOffset terminal.1 slot with
    ⟨laneX, laneY⟩
  simp [Cell.add, add_assoc]

/-- Delayed-lane radial outer routes commute with translation of their
center. -/
theorem retainedTerminalFanOuterEscapedRadialRoute_translatePolyline
    (offset center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    translatePolyline offset
        (retainedTerminalFanOuterEscapedRadialRoute
          center terminal slot) =
      retainedTerminalFanOuterEscapedRadialRoute
        (Cell.add offset center) terminal slot := by
  unfold retainedTerminalFanOuterEscapedRadialRoute
  dsimp only
  rw [translatePolyline_joinAtEndpoint,
    translatePolyline_joinAtEndpoint,
    RetainedRay.rasterize_translatePolyline,
    retainedTerminalFanOuterLaneShiftRouteAt_translatePolyline,
    RetainedRay.rasterize_translatePolyline,
    retainedAngularFanOuterDemand_gate_add,
    retainedTerminalFanOuterSourceEscapePoint_add]
  congr 2
  rcases offset with ⟨offsetX, offsetY⟩
  rcases retainedTerminalFanOuterSourceEscapePoint
      center terminal slot with
    ⟨escapeX, escapeY⟩
  rcases retainedTerminalFanOuterLaneOffset terminal.1 slot with
    ⟨laneX, laneY⟩
  simp [Cell.add, add_assoc]

/-- Ordinary complete outer routes commute with translation of their
center. -/
theorem retainedTerminalFanOuterCompleteRoute_translatePolyline
    (offset center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    translatePolyline offset
        (retainedTerminalFanOuterCompleteRoute center terminal slot) =
      retainedTerminalFanOuterCompleteRoute
        (Cell.add offset center) terminal slot := by
  unfold retainedTerminalFanOuterCompleteRoute
  rw [translatePolyline_joinAtEndpoint,
    retainedTerminalFanOuterRadialRoute_translatePolyline,
    retainedTerminalFanOuterLocalRouteAt_translatePolyline]

/-- Delayed-lane complete outer routes commute with translation of their
center. -/
theorem retainedTerminalFanOuterEscapedCompleteRoute_translatePolyline
    (offset center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    translatePolyline offset
        (retainedTerminalFanOuterEscapedCompleteRoute
          center terminal slot) =
      retainedTerminalFanOuterEscapedCompleteRoute
        (Cell.add offset center) terminal slot := by
  unfold retainedTerminalFanOuterEscapedCompleteRoute
  rw [translatePolyline_joinAtEndpoint,
    retainedTerminalFanOuterEscapedRadialRoute_translatePolyline,
    retainedTerminalFanOuterLocalRouteAt_translatePolyline]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
