import LeanTrominoes.RetainedAngularFanAnnulusDemands
import LeanTrominoes.OrthogonalPolylineJoin

/-!
# Finite orthogonal witnesses across the retained fan annulus

Every fan-annulus demand has a concrete orthogonal route inside the fixed
radius-36 interface and outside the radius-21 square.  The witness first
moves one unit outward from its radius-33 fan port, follows the radius-34
square counterclockwise to the east cut, and then follows that square
clockwise to the radial approach for its radius-22 compass anchor.

These routes deliberately establish only the individual finite routing
problem: different witnesses share the east cut.  A coordinated finite
router will select separated representatives while reusing the endpoint,
orthogonality, and annular-boundary interface established here.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

private instance orthogonalPolylineDecidable
    (points : List Cell) :
    Decidable
      (PeriodicOrthocrossing.OrthogonalPolyline points) := by
  unfold PeriodicOrthocrossing.OrthogonalPolyline
  infer_instance

/-- Common cut used by the elementary individual annular witnesses. -/
def retainedTerminalFanAnnulusCut : Cell := (34, 0)

/-- Route from a radius-33 fan port to the east cut on the radius-34 square.
The duplicate-removal handles the due-east port, whose outward projection is
already the cut. -/
def retainedTerminalFanPortToAnnulusCut
    (port : RetainedTerminalAdapterPort) : List Cell :=
  let outer := retainedTerminalFanPortOffset port
  (if port.val < 12 then
      [outer, (34, outer.2), retainedTerminalFanAnnulusCut]
    else if port.val < 34 then
      [outer, (outer.1, 34), (34, 34),
        retainedTerminalFanAnnulusCut]
    else if port.val < 56 then
      [outer, (-34, outer.2), (-34, 34), (34, 34),
        retainedTerminalFanAnnulusCut]
    else if port.val < 78 then
      [outer, (outer.1, -34), (-34, -34), (-34, 34), (34, 34),
        retainedTerminalFanAnnulusCut]
    else
      [outer, (34, outer.2), (34, -34), (-34, -34), (-34, 34),
        (34, 34), retainedTerminalFanAnnulusCut]).dedup

/-- Route from the east radius-34 cut to one radius-22 compass anchor. -/
def retainedTerminalFanAnnulusCutToAnchor
    (slot : RetainedTerminalSlot) : List Cell :=
  let inner :=
    retainedTerminalAdapterPortOffset
      (retainedTerminalFanAnchorPort slot)
  if slot.val = 0 then
    [retainedTerminalFanAnnulusCut, inner]
  else if slot.val = 1 then
    [retainedTerminalFanAnnulusCut, (34, 22), inner]
  else if slot.val = 2 then
    [retainedTerminalFanAnnulusCut, (34, 34), (0, 34), inner]
  else if slot.val = 3 then
    [retainedTerminalFanAnnulusCut, (34, 34), (-22, 34), inner]
  else if slot.val = 4 then
    [retainedTerminalFanAnnulusCut, (34, 34), (-34, 34), (-34, 0),
      inner]
  else if slot.val = 5 then
    [retainedTerminalFanAnnulusCut, (34, 34), (-34, 34), (-34, -22),
      inner]
  else if slot.val = 6 then
    [retainedTerminalFanAnnulusCut, (34, 34), (-34, 34), (-34, -34),
      (0, -34), inner]
  else
    [retainedTerminalFanAnnulusCut, (34, 34), (-34, 34), (-34, -34),
      (22, -34), inner]

/-- Elementary finite orthogonal witness for one outer port and one compass
anchor.  Coordinated routing will replace the shared-cut choice. -/
def retainedTerminalFanAnnulusWitnessRoute
    (port : RetainedTerminalAdapterPort)
    (slot : RetainedTerminalSlot) : List Cell :=
  joinAtEndpoint
    (retainedTerminalFanPortToAnnulusCut port)
    (retainedTerminalFanAnnulusCutToAnchor slot)

/-- The outer half starts at its exact radius-33 fan port. -/
@[simp]
theorem retainedTerminalFanPortToAnnulusCut_head? :
    ∀ port : RetainedTerminalAdapterPort,
      (retainedTerminalFanPortToAnnulusCut port).head? =
        some (retainedTerminalFanPortOffset port) := by
  native_decide

/-- The outer half ends at the common radius-34 cut. -/
@[simp]
theorem retainedTerminalFanPortToAnnulusCut_getLast? :
    ∀ port : RetainedTerminalAdapterPort,
      (retainedTerminalFanPortToAnnulusCut port).getLast? =
        some retainedTerminalFanAnnulusCut := by
  native_decide

/-- Every outer-to-cut witness is orthogonal. -/
theorem retainedTerminalFanPortToAnnulusCut_orthogonal :
    ∀ port : RetainedTerminalAdapterPort,
      PeriodicOrthocrossing.OrthogonalPolyline
        (retainedTerminalFanPortToAnnulusCut port) := by
  native_decide

/-- The inward half starts at the common radius-34 cut. -/
@[simp]
theorem retainedTerminalFanAnnulusCutToAnchor_head? :
    ∀ slot : RetainedTerminalSlot,
      (retainedTerminalFanAnnulusCutToAnchor slot).head? =
        some retainedTerminalFanAnnulusCut := by
  native_decide

/-- The inward half ends at its exact radius-22 compass anchor. -/
@[simp]
theorem retainedTerminalFanAnnulusCutToAnchor_getLast? :
    ∀ slot : RetainedTerminalSlot,
      (retainedTerminalFanAnnulusCutToAnchor slot).getLast? =
        some
          (retainedTerminalAdapterPortOffset
            (retainedTerminalFanAnchorPort slot)) := by
  native_decide

/-- Every cut-to-anchor witness is orthogonal. -/
theorem retainedTerminalFanAnnulusCutToAnchor_orthogonal :
    ∀ slot : RetainedTerminalSlot,
      PeriodicOrthocrossing.OrthogonalPolyline
        (retainedTerminalFanAnnulusCutToAnchor slot) := by
  native_decide

/-- Every complete witness starts at its requested outer port. -/
@[simp]
theorem retainedTerminalFanAnnulusWitnessRoute_head?
    (port : RetainedTerminalAdapterPort)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanAnnulusWitnessRoute port slot).head? =
      some (retainedTerminalFanPortOffset port) := by
  exact joinAtEndpoint_head?
    (retainedTerminalFanPortToAnnulusCut_head? port)

/-- Every complete witness ends at its requested compass anchor. -/
@[simp]
theorem retainedTerminalFanAnnulusWitnessRoute_getLast?
    (port : RetainedTerminalAdapterPort)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanAnnulusWitnessRoute port slot).getLast? =
      some
        (retainedTerminalAdapterPortOffset
          (retainedTerminalFanAnchorPort slot)) := by
  exact joinAtEndpoint_getLast?
    (retainedTerminalFanPortToAnnulusCut_getLast? port)
    (retainedTerminalFanAnnulusCutToAnchor_head? slot)
    (retainedTerminalFanAnnulusCutToAnchor_getLast? slot)

/-- Every complete annular witness is an orthogonal polyline. -/
theorem retainedTerminalFanAnnulusWitnessRoute_orthogonal
    (port : RetainedTerminalAdapterPort)
    (slot : RetainedTerminalSlot) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (retainedTerminalFanAnnulusWitnessRoute port slot) := by
  exact
    PeriodicOrthocrossing.OrthogonalPolyline.joinAtEndpoint
      (retainedTerminalFanPortToAnnulusCut_orthogonal port)
      (retainedTerminalFanAnnulusCutToAnchor_orthogonal slot)
      (retainedTerminalFanPortToAnnulusCut_getLast? port)
      (retainedTerminalFanAnnulusCutToAnchor_head? slot)

/-- Every listed witness point remains inside the retained radius-36
interface and strictly outside the radius-21 square. -/
theorem retainedTerminalFanAnnulusWitnessRoute_points_in_shell :
    ∀ (port : RetainedTerminalAdapterPort)
      (slot : RetainedTerminalSlot) (point : Cell),
      point ∈ retainedTerminalFanAnnulusWitnessRoute port slot →
        WithinCoordinateRadius 36 (0, 0) point ∧
          ¬ WithinCoordinateRadius 21 (0, 0) point := by
  native_decide

/-- Optional elementary witness selected by one finite shape slot. -/
def RetainedAngularTerminalShape.fanAnnulusWitnessRoute
    (shape : RetainedAngularTerminalShape)
    (slot : RetainedTerminalSlot) : Option (List Cell) :=
  (shape.fanPort slot).map fun port =>
    retainedTerminalFanAnnulusWitnessRoute port slot

/-- An active slot selects the witness with its exact direction-and-slot
outer port. -/
theorem RetainedAngularTerminalShape.fanAnnulusWitnessRoute_eq_some
    (shape : RetainedAngularTerminalShape)
    (slot : RetainedTerminalSlot)
    (direction : RetainedTerminalDirection)
    (directionEq : shape.direction slot = some direction) :
    shape.fanAnnulusWitnessRoute slot =
      some
        (retainedTerminalFanAnnulusWitnessRoute
          (retainedTerminalFanPort direction slot) slot) := by
  simp [fanAnnulusWitnessRoute,
    shape.fanPort_eq_some slot direction directionEq]

/-- Inactive slots select no annular witness. -/
theorem RetainedAngularTerminalShape.fanAnnulusWitnessRoute_eq_none
    (shape : RetainedAngularTerminalShape)
    (slot : RetainedTerminalSlot)
    (directionEq : shape.direction slot = none) :
    shape.fanAnnulusWitnessRoute slot = none := by
  simp [fanAnnulusWitnessRoute,
    RetainedAngularTerminalShape.fanPort, directionEq]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
