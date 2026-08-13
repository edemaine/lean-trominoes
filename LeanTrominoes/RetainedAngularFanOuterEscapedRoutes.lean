/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanOuterCompleteRoutes

/-!
# Source-escaped retained outer fan routes

The ordinary outer radial route applies its occurrence-lane shift at the
source gate.  That is suitable for separating several gates around one
variable center, but two direct incidences leaving one clause can have the
same gate.  If their direction-specific lane steps agree, the two shifts can
then overlap beyond the common head.

This layer splits off the first 64 primitive blocks before the same lane
shift and remaining radial tail.  Sixty-four blocks exceed the maximum lane
displacement of `8 * 7 = 56`.  At the concrete source scale four, even a
unit compass terminal has 288 radial blocks outside the fixed fan interface,
so the escape fits with ample room.

The default route below rasterizes that escape independently.  Its endpoint
and orthogonality facts are useful, but independent rasterization is not by
itself a shared-clause planarity certificate: some compass triples and
routed-clause pairs choose the same first grid step.  Direct component
families therefore supply coordinated escape prefixes through the certified
interface developed below.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

set_option maxRecDepth 4096

/-- Number of primitive blocks retained before an occurrence lane shifts. -/
def retainedTerminalFanOuterSourceEscapeLength : Nat := 64

/-- An inward ray in a specified retained terminal direction and length. -/
def retainedTerminalFanOuterInwardRayOfLength
    (direction : RetainedTerminalDirection)
    (length : Nat) : RetainedRay :=
  match direction with
  | .compass port =>
      .compass (oppositePort port) length
  | .routedClause arm =>
      .routedClause arm length

/-- The fixed source-escape portion of an outer inward ray. -/
def retainedTerminalFanOuterSourceEscapeRay
    (terminal : RetainedTerminalData) : RetainedRay :=
  retainedTerminalFanOuterInwardRayOfLength terminal.1
    retainedTerminalFanOuterSourceEscapeLength

/-- The radial tail left after the fixed source escape. -/
def retainedTerminalFanOuterEscapedRemainingRay
    (terminal : RetainedTerminalData) : RetainedRay :=
  retainedTerminalFanOuterInwardRayOfLength terminal.1
    (retainedTerminalFanOuterRadialLength terminal -
      retainedTerminalFanOuterSourceEscapeLength)

/-- Splitting after the source escape preserves the total inward
displacement. -/
theorem retainedTerminalFanOuterEscapedRay_vectors_add
    (terminal : RetainedTerminalData)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal) :
    Cell.add
        (retainedTerminalFanOuterSourceEscapeRay terminal).vector
        (retainedTerminalFanOuterEscapedRemainingRay terminal).vector =
      (retainedTerminalFanOuterInwardRay terminal).vector := by
  rcases terminal with ⟨direction, length⟩
  cases direction with
  | compass port =>
      cases port <;>
        simp [retainedTerminalFanOuterSourceEscapeRay,
          retainedTerminalFanOuterEscapedRemainingRay,
          retainedTerminalFanOuterInwardRayOfLength,
          retainedTerminalFanOuterInwardRay,
          retainedTerminalFanOuterRadialLength,
          retainedTerminalFanOuterSourceEscapeLength,
          retainedTerminalInterfaceMultiplier,
          RetainedRay.vector, oppositePort,
          OccurrenceSplitRing.Port.unitVector,
          Cell.add, Cell.scale] at escapeFits ⊢ <;>
        omega
  | routedClause arm =>
      cases arm <;>
        simp [retainedTerminalFanOuterSourceEscapeRay,
          retainedTerminalFanOuterEscapedRemainingRay,
          retainedTerminalFanOuterInwardRayOfLength,
          retainedTerminalFanOuterInwardRay,
          retainedTerminalFanOuterRadialLength,
          retainedTerminalFanOuterSourceEscapeLength,
          retainedTerminalInterfaceMultiplier,
          RetainedRay.vector, routedClauseRayPrimitive,
          Cell.add, Cell.scale] at escapeFits ⊢ <;>
        omega

/-- At source scale four, every positive retained terminal has room for the
fixed escape before the radius-288 interface. -/
theorem retainedTerminalFanOuterSourceEscape_fits_scale_four
    (terminal : RetainedTerminalData)
    (lengthPositive : 0 < terminal.2) :
    retainedTerminalFanOuterSourceEscapeLength ≤
      retainedTerminalFanOuterRadialLength
        (scaleRetainedTerminalData 4 terminal) := by
  rcases terminal with ⟨direction, length⟩
  cases direction with
  | compass port =>
      cases port <;>
        simp [scaleRetainedTerminalData,
          retainedTerminalFanOuterSourceEscapeLength,
          retainedTerminalFanOuterRadialLength,
          retainedTerminalFanTotalRefinement,
          PeriodicEightOccurrenceSplitPositioned.refinementScale,
          retainedTerminalFanRoutingRefinement,
          retainedTerminalInterfaceMultiplier] at lengthPositive ⊢ <;>
        omega
  | routedClause arm =>
      cases arm <;>
        simp [scaleRetainedTerminalData,
          retainedTerminalFanOuterSourceEscapeLength,
          retainedTerminalFanOuterRadialLength,
          retainedTerminalFanTotalRefinement,
          PeriodicEightOccurrenceSplitPositioned.refinementScale,
          retainedTerminalFanRoutingRefinement,
          retainedTerminalInterfaceMultiplier] at lengthPositive ⊢ <;>
        omega

/-- The point at which an escaped route applies its occurrence-lane shift. -/
def retainedTerminalFanOuterSourceEscapePoint
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) : Cell :=
  Cell.add
    (retainedAngularFanOuterDemand center terminal slot).gate
    (retainedTerminalFanOuterSourceEscapeRay terminal).vector

/-- Radial route that leaves a shared source gate before selecting its
parallel occurrence lane. -/
def retainedTerminalFanOuterEscapedRadialRoute
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) : List Cell :=
  let gate :=
    (retainedAngularFanOuterDemand center terminal slot).gate
  let escapePoint :=
    retainedTerminalFanOuterSourceEscapePoint center terminal slot
  let shiftedEscapePoint :=
    Cell.add escapePoint
      (retainedTerminalFanOuterLaneOffset terminal.1 slot)
  joinAtEndpoint
    ((retainedTerminalFanOuterSourceEscapeRay terminal).rasterize gate)
    (joinAtEndpoint
      (retainedTerminalFanOuterLaneShiftRouteAt
        escapePoint terminal.1 slot)
      ((retainedTerminalFanOuterEscapedRemainingRay terminal).rasterize
        shiftedEscapePoint))

/-- An escaped radial route begins at the unchanged exact source gate. -/
@[simp]
theorem retainedTerminalFanOuterEscapedRadialRoute_head?
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanOuterEscapedRadialRoute
      center terminal slot).head? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).gate := by
  unfold retainedTerminalFanOuterEscapedRadialRoute
  apply joinAtEndpoint_head?
  exact RetainedRay.rasterize_head? _ _

/-- If the escape fits, the escaped radial route reaches the same
radius-288 occurrence lane port as the ordinary radial route. -/
@[simp]
theorem retainedTerminalFanOuterEscapedRadialRoute_getLast?
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal) :
    (retainedTerminalFanOuterEscapedRadialRoute
      center terminal slot).getLast? =
        some
          (retainedTerminalFanOuterLanePort
            center terminal.1 slot) := by
  let gate :=
    (retainedAngularFanOuterDemand center terminal slot).gate
  let escapePoint :=
    retainedTerminalFanOuterSourceEscapePoint center terminal slot
  let shiftedEscapePoint :=
    Cell.add escapePoint
      (retainedTerminalFanOuterLaneOffset terminal.1 slot)
  have escapePointEq :
      escapePoint =
        Cell.add gate
          (retainedTerminalFanOuterSourceEscapeRay terminal).vector := by
    rfl
  have shiftedEscapePointEq :
      shiftedEscapePoint =
        Cell.add escapePoint
          (retainedTerminalFanOuterLaneOffset terminal.1 slot) := by
    rfl
  have escapeLast :
      ((retainedTerminalFanOuterSourceEscapeRay terminal).rasterize
        gate).getLast? = some escapePoint := by
    rw [RetainedRay.rasterize_getLast?]
    rfl
  have remainingLast :
      ((retainedTerminalFanOuterEscapedRemainingRay terminal).rasterize
        shiftedEscapePoint).getLast? =
          some
            (retainedTerminalFanOuterLanePort
              center terminal.1 slot) := by
    rw [RetainedRay.rasterize_getLast?]
    have ordinaryLast :=
      retainedTerminalFanOuterInwardRay_getLast?
        center terminal slot lengthPositive
    rw [RetainedRay.rasterize_getLast?] at ordinaryLast
    apply congrArg some
    calc
      Cell.add shiftedEscapePoint
          (retainedTerminalFanOuterEscapedRemainingRay terminal).vector =
        Cell.add
          (Cell.add gate
            (retainedTerminalFanOuterLaneOffset terminal.1 slot))
          (retainedTerminalFanOuterInwardRay terminal).vector := by
            rw [shiftedEscapePointEq, escapePointEq]
            rw [← retainedTerminalFanOuterEscapedRay_vectors_add
              terminal escapeFits]
            rcases gate with ⟨gateX, gateY⟩
            rcases
                (retainedTerminalFanOuterSourceEscapeRay terminal).vector with
              ⟨escapeX, escapeY⟩
            rcases
                (retainedTerminalFanOuterEscapedRemainingRay terminal).vector with
              ⟨remainingX, remainingY⟩
            rcases retainedTerminalFanOuterLaneOffset terminal.1 slot with
              ⟨offsetX, offsetY⟩
            simp [Cell.add]
            constructor <;> ring
      _ = retainedTerminalFanOuterLanePort
          center terminal.1 slot :=
        Option.some.inj ordinaryLast
  unfold retainedTerminalFanOuterEscapedRadialRoute
  change
    (joinAtEndpoint
      ((retainedTerminalFanOuterSourceEscapeRay terminal).rasterize gate)
      (joinAtEndpoint
        (retainedTerminalFanOuterLaneShiftRouteAt
          escapePoint terminal.1 slot)
        ((retainedTerminalFanOuterEscapedRemainingRay terminal).rasterize
          shiftedEscapePoint))).getLast? =
      some
        (retainedTerminalFanOuterLanePort
          center terminal.1 slot)
  apply joinAtEndpoint_getLast? escapeLast
  · apply joinAtEndpoint_head?
    exact retainedTerminalFanOuterLaneShiftRouteAt_head?
      escapePoint terminal.1 slot
  · apply joinAtEndpoint_getLast?
      (retainedTerminalFanOuterLaneShiftRouteAt_getLast?
        escapePoint terminal.1 slot)
      (RetainedRay.rasterize_head?
        (retainedTerminalFanOuterEscapedRemainingRay terminal)
        shiftedEscapePoint)
      remainingLast

/-- Escaping, shifting, and following the remaining raster are all
orthogonal endpoint joins. -/
theorem retainedTerminalFanOuterEscapedRadialRoute_orthogonal
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (retainedTerminalFanOuterEscapedRadialRoute
        center terminal slot) := by
  let gate :=
    (retainedAngularFanOuterDemand center terminal slot).gate
  let escapePoint :=
    retainedTerminalFanOuterSourceEscapePoint center terminal slot
  let shiftedEscapePoint :=
    Cell.add escapePoint
      (retainedTerminalFanOuterLaneOffset terminal.1 slot)
  have shiftedTailOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline
        (joinAtEndpoint
          (retainedTerminalFanOuterLaneShiftRouteAt
            escapePoint terminal.1 slot)
          ((retainedTerminalFanOuterEscapedRemainingRay terminal).rasterize
            shiftedEscapePoint)) := by
    exact
      (retainedTerminalFanOuterLaneShiftRouteAt_orthogonal
        escapePoint terminal.1 slot).joinAtEndpoint
        (RetainedRay.rasterize_orthogonal
          (retainedTerminalFanOuterEscapedRemainingRay terminal)
          shiftedEscapePoint)
        (retainedTerminalFanOuterLaneShiftRouteAt_getLast?
          escapePoint terminal.1 slot)
        (RetainedRay.rasterize_head?
          (retainedTerminalFanOuterEscapedRemainingRay terminal)
          shiftedEscapePoint)
  unfold retainedTerminalFanOuterEscapedRadialRoute
  exact
    (RetainedRay.rasterize_orthogonal
      (retainedTerminalFanOuterSourceEscapeRay terminal)
      gate).joinAtEndpoint
      shiftedTailOrthogonal
      (by
        rw [RetainedRay.rasterize_getLast?])
      (by
        apply joinAtEndpoint_head?
        exact retainedTerminalFanOuterLaneShiftRouteAt_head?
          escapePoint terminal.1 slot)

/-- A clause-level source escape supplies an orthogonal route from the
common gate to the fixed checkpoint on this terminal ray.  Pairwise
planarity belongs to the family that supplies several such certificates. -/
structure RetainedTerminalFanOuterSourceEscapeCertificate
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) where
  route : List Cell
  head_eq :
    route.head? =
      some
        (retainedAngularFanOuterDemand
          center terminal slot).gate
  last_eq :
    route.getLast? =
      some
        (retainedTerminalFanOuterSourceEscapePoint
          center terminal slot)
  orthogonal :
    PeriodicOrthocrossing.OrthogonalPolyline route

/-- Independent rasterization provides the canonical one-route escape
certificate.  Shared-clause families may replace it with a coordinated
route having the same endpoints. -/
def retainedTerminalFanOuterRasterizedSourceEscapeCertificate
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    RetainedTerminalFanOuterSourceEscapeCertificate
      center terminal slot where
  route :=
    (retainedTerminalFanOuterSourceEscapeRay terminal).rasterize
      (retainedAngularFanOuterDemand center terminal slot).gate
  head_eq := RetainedRay.rasterize_head? _ _
  last_eq := by
    rw [RetainedRay.rasterize_getLast?]
    rfl
  orthogonal := RetainedRay.rasterize_orthogonal _ _

/-- The part of an escaped radial route after its clause-coordinated source
escape: select the occurrence lane and follow the remaining old raster. -/
def retainedTerminalFanOuterEscapedShiftedTail
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) : List Cell :=
  let escapePoint :=
    retainedTerminalFanOuterSourceEscapePoint center terminal slot
  let shiftedEscapePoint :=
    Cell.add escapePoint
      (retainedTerminalFanOuterLaneOffset terminal.1 slot)
  joinAtEndpoint
    (retainedTerminalFanOuterLaneShiftRouteAt
      escapePoint terminal.1 slot)
    ((retainedTerminalFanOuterEscapedRemainingRay terminal).rasterize
      shiftedEscapePoint)

/-- The shifted tail starts where every certified source escape ends. -/
@[simp]
theorem retainedTerminalFanOuterEscapedShiftedTail_head?
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanOuterEscapedShiftedTail
      center terminal slot).head? =
        some
          (retainedTerminalFanOuterSourceEscapePoint
            center terminal slot) := by
  unfold retainedTerminalFanOuterEscapedShiftedTail
  apply joinAtEndpoint_head?
  exact retainedTerminalFanOuterLaneShiftRouteAt_head? _ _ _

/-- The shifted tail reaches the unchanged radius-288 lane port. -/
@[simp]
theorem retainedTerminalFanOuterEscapedShiftedTail_getLast?
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal) :
    (retainedTerminalFanOuterEscapedShiftedTail
      center terminal slot).getLast? =
        some
          (retainedTerminalFanOuterLanePort
            center terminal.1 slot) := by
  let gate :=
    (retainedAngularFanOuterDemand center terminal slot).gate
  let escapePoint :=
    retainedTerminalFanOuterSourceEscapePoint center terminal slot
  let shiftedEscapePoint :=
    Cell.add escapePoint
      (retainedTerminalFanOuterLaneOffset terminal.1 slot)
  have escapePointEq :
      escapePoint =
        Cell.add gate
          (retainedTerminalFanOuterSourceEscapeRay terminal).vector := by
    rfl
  have shiftedEscapePointEq :
      shiftedEscapePoint =
        Cell.add escapePoint
          (retainedTerminalFanOuterLaneOffset terminal.1 slot) := by
    rfl
  have remainingLast :
      ((retainedTerminalFanOuterEscapedRemainingRay terminal).rasterize
        shiftedEscapePoint).getLast? =
          some
            (retainedTerminalFanOuterLanePort
              center terminal.1 slot) := by
    rw [RetainedRay.rasterize_getLast?]
    have ordinaryLast :=
      retainedTerminalFanOuterInwardRay_getLast?
        center terminal slot lengthPositive
    rw [RetainedRay.rasterize_getLast?] at ordinaryLast
    apply congrArg some
    calc
      Cell.add shiftedEscapePoint
          (retainedTerminalFanOuterEscapedRemainingRay terminal).vector =
        Cell.add
          (Cell.add gate
            (retainedTerminalFanOuterLaneOffset terminal.1 slot))
          (retainedTerminalFanOuterInwardRay terminal).vector := by
            rw [shiftedEscapePointEq, escapePointEq]
            rw [← retainedTerminalFanOuterEscapedRay_vectors_add
              terminal escapeFits]
            rcases gate with ⟨gateX, gateY⟩
            rcases
                (retainedTerminalFanOuterSourceEscapeRay terminal).vector with
              ⟨escapeX, escapeY⟩
            rcases
                (retainedTerminalFanOuterEscapedRemainingRay terminal).vector with
              ⟨remainingX, remainingY⟩
            rcases retainedTerminalFanOuterLaneOffset terminal.1 slot with
              ⟨offsetX, offsetY⟩
            simp [Cell.add]
            constructor <;> ring
      _ = retainedTerminalFanOuterLanePort
          center terminal.1 slot :=
        Option.some.inj ordinaryLast
  unfold retainedTerminalFanOuterEscapedShiftedTail
  exact joinAtEndpoint_getLast?
    (retainedTerminalFanOuterLaneShiftRouteAt_getLast?
      escapePoint terminal.1 slot)
    (RetainedRay.rasterize_head?
      (retainedTerminalFanOuterEscapedRemainingRay terminal)
      shiftedEscapePoint)
    remainingLast

/-- The shifted remainder is orthogonal independently of the selected
clause-level escape. -/
theorem retainedTerminalFanOuterEscapedShiftedTail_orthogonal
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (retainedTerminalFanOuterEscapedShiftedTail
        center terminal slot) := by
  let escapePoint :=
    retainedTerminalFanOuterSourceEscapePoint center terminal slot
  let shiftedEscapePoint :=
    Cell.add escapePoint
      (retainedTerminalFanOuterLaneOffset terminal.1 slot)
  unfold retainedTerminalFanOuterEscapedShiftedTail
  exact
    (retainedTerminalFanOuterLaneShiftRouteAt_orthogonal
      escapePoint terminal.1 slot).joinAtEndpoint
      (RetainedRay.rasterize_orthogonal
        (retainedTerminalFanOuterEscapedRemainingRay terminal)
        shiftedEscapePoint)
      (retainedTerminalFanOuterLaneShiftRouteAt_getLast?
        escapePoint terminal.1 slot)
      (RetainedRay.rasterize_head?
        (retainedTerminalFanOuterEscapedRemainingRay terminal)
        shiftedEscapePoint)

/-- Use any certified clause-coordinated escape before the common shifted
radial tail. -/
def retainedTerminalFanOuterCoordinatedEscapedRadialRoute
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (escape :
      RetainedTerminalFanOuterSourceEscapeCertificate
        center terminal slot) : List Cell :=
  joinAtEndpoint escape.route
    (retainedTerminalFanOuterEscapedShiftedTail
      center terminal slot)

@[simp]
theorem retainedTerminalFanOuterCoordinatedEscapedRadialRoute_head?
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (escape :
      RetainedTerminalFanOuterSourceEscapeCertificate
        center terminal slot) :
    (retainedTerminalFanOuterCoordinatedEscapedRadialRoute
      center terminal slot escape).head? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).gate := by
  exact joinAtEndpoint_head? escape.head_eq

@[simp]
theorem retainedTerminalFanOuterCoordinatedEscapedRadialRoute_getLast?
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (escape :
      RetainedTerminalFanOuterSourceEscapeCertificate
        center terminal slot)
    (lengthPositive : 0 < terminal.2)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal) :
    (retainedTerminalFanOuterCoordinatedEscapedRadialRoute
      center terminal slot escape).getLast? =
        some
          (retainedTerminalFanOuterLanePort
            center terminal.1 slot) := by
  exact joinAtEndpoint_getLast?
    escape.last_eq
    (retainedTerminalFanOuterEscapedShiftedTail_head?
      center terminal slot)
    (retainedTerminalFanOuterEscapedShiftedTail_getLast?
      center terminal slot lengthPositive escapeFits)

theorem retainedTerminalFanOuterCoordinatedEscapedRadialRoute_orthogonal
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (escape :
      RetainedTerminalFanOuterSourceEscapeCertificate
        center terminal slot) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (retainedTerminalFanOuterCoordinatedEscapedRadialRoute
        center terminal slot escape) := by
  exact escape.orthogonal.joinAtEndpoint
    (retainedTerminalFanOuterEscapedShiftedTail_orthogonal
      center terminal slot)
    escape.last_eq
    (retainedTerminalFanOuterEscapedShiftedTail_head?
      center terminal slot)

/-- A coordinated escape changes only the source-side prefix of the complete
outer fan route. -/
def retainedTerminalFanOuterCoordinatedEscapedCompleteRoute
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (escape :
      RetainedTerminalFanOuterSourceEscapeCertificate
        center terminal slot) : List Cell :=
  joinAtEndpoint
    (retainedTerminalFanOuterCoordinatedEscapedRadialRoute
      center terminal slot escape)
    (retainedTerminalFanOuterLocalRouteAt
      center terminal.1 slot)

@[simp]
theorem retainedTerminalFanOuterCoordinatedEscapedCompleteRoute_head?
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (escape :
      RetainedTerminalFanOuterSourceEscapeCertificate
        center terminal slot) :
    (retainedTerminalFanOuterCoordinatedEscapedCompleteRoute
      center terminal slot escape).head? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).gate := by
  exact joinAtEndpoint_head?
    (retainedTerminalFanOuterCoordinatedEscapedRadialRoute_head?
      center terminal slot escape)

@[simp]
theorem retainedTerminalFanOuterCoordinatedEscapedCompleteRoute_getLast?
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (escape :
      RetainedTerminalFanOuterSourceEscapeCertificate
        center terminal slot)
    (lengthPositive : 0 < terminal.2)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal) :
    (retainedTerminalFanOuterCoordinatedEscapedCompleteRoute
      center terminal slot escape).getLast? =
        some
          (Cell.add center
            (Cell.scale retainedTerminalFanRoutingRefinement
              (angularFanBoundaryOffset slot.val))) := by
  exact joinAtEndpoint_getLast?
    (retainedTerminalFanOuterCoordinatedEscapedRadialRoute_getLast?
      center terminal slot escape lengthPositive escapeFits)
    (retainedTerminalFanOuterLocalRouteAt_head?
      center terminal.1 slot)
    (retainedTerminalFanOuterLocalRouteAt_getLast?
      center terminal.1 slot)

theorem retainedTerminalFanOuterCoordinatedEscapedCompleteRoute_orthogonal
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (escape :
      RetainedTerminalFanOuterSourceEscapeCertificate
        center terminal slot)
    (lengthPositive : 0 < terminal.2)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (retainedTerminalFanOuterCoordinatedEscapedCompleteRoute
        center terminal slot escape) := by
  exact
    (retainedTerminalFanOuterCoordinatedEscapedRadialRoute_orthogonal
      center terminal slot escape).joinAtEndpoint
      (retainedTerminalFanOuterLocalRouteAt_orthogonal
        center terminal.1 slot)
      (retainedTerminalFanOuterCoordinatedEscapedRadialRoute_getLast?
        center terminal slot escape lengthPositive escapeFits)
      (retainedTerminalFanOuterLocalRouteAt_head?
        center terminal.1 slot)

/-- Complete escaped route from a source gate to its unchanged Figure 7
boundary occurrence. -/
def retainedTerminalFanOuterEscapedCompleteRoute
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) : List Cell :=
  joinAtEndpoint
    (retainedTerminalFanOuterEscapedRadialRoute
      center terminal slot)
    (retainedTerminalFanOuterLocalRouteAt
      center terminal.1 slot)

/-- A complete escaped route retains the exact source gate. -/
@[simp]
theorem retainedTerminalFanOuterEscapedCompleteRoute_head?
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot) :
    (retainedTerminalFanOuterEscapedCompleteRoute
      center terminal slot).head? =
        some
          (retainedAngularFanOuterDemand
            center terminal slot).gate := by
  exact joinAtEndpoint_head?
    (retainedTerminalFanOuterEscapedRadialRoute_head?
      center terminal slot)

/-- A positive escaped route with enough radial length retains the exact
Figure 7 boundary endpoint. -/
@[simp]
theorem retainedTerminalFanOuterEscapedCompleteRoute_getLast?
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal) :
    (retainedTerminalFanOuterEscapedCompleteRoute
      center terminal slot).getLast? =
        some
          (Cell.add center
            (Cell.scale retainedTerminalFanRoutingRefinement
              (angularFanBoundaryOffset slot.val))) := by
  exact joinAtEndpoint_getLast?
    (retainedTerminalFanOuterEscapedRadialRoute_getLast?
      center terminal slot lengthPositive escapeFits)
    (retainedTerminalFanOuterLocalRouteAt_head?
      center terminal.1 slot)
    (retainedTerminalFanOuterLocalRouteAt_getLast?
      center terminal.1 slot)

/-- The complete source-escaped route is orthogonal whenever its radial
escape reaches the ordinary interface port. -/
theorem retainedTerminalFanOuterEscapedCompleteRoute_orthogonal
    (center : Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (lengthPositive : 0 < terminal.2)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength terminal) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (retainedTerminalFanOuterEscapedCompleteRoute
        center terminal slot) := by
  exact
    (retainedTerminalFanOuterEscapedRadialRoute_orthogonal
      center terminal slot).joinAtEndpoint
      (retainedTerminalFanOuterLocalRouteAt_orthogonal
        center terminal.1 slot)
      (retainedTerminalFanOuterEscapedRadialRoute_getLast?
        center terminal slot lengthPositive escapeFits)
      (retainedTerminalFanOuterLocalRouteAt_head?
        center terminal.1 slot)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
