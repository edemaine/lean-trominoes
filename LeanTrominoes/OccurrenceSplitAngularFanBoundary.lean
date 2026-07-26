import LeanTrominoes.OccurrenceSplitAngularFanInstantiation
import LeanTrominoes.PeriodicOrthocrossingOrthogonal

/-!
# Splice boundaries of positioned angular fans

The global copied-clause route does not need to know the internal Figure 7
geometry.  For each angular-list index it only needs a boundary point and a
local route suffix from that point to the selected occurrence copy.

This file exposes that interface and proves exact endpoints, orthogonality,
and equality with the corresponding route in the certified instantiated
fan.  The remaining global routing problem is therefore cleanly separated:
route each old clause incidence to its declared fan boundary point.
-/

namespace LeanTrominoes
namespace OccurrenceSplitRing

open PlanarThreeSAT
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

/-- Boundary point where the copied source incidence at angular index
`index` enters its positioned Figure 7 macrocell. -/
def angularFanBoundaryPosition
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) (index : Nat) : Cell :=
  Cell.add
    (macroOrigin sourcePlacement atom)
    (spokeClausePosition (angularPortOfIndex index))

/-- Certified local suffix from an angular fan boundary point to the
selected fixed-eight occurrence copy. -/
def angularFanSpokeRoute
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) (index : Nat) : List Cell :=
  (spokeRoute (angularPortOfIndex index)).map
    (Cell.add (macroOrigin sourcePlacement atom))

@[simp]
theorem spokeRoute_head? (port : Port) :
    (spokeRoute port).head? =
      some (spokeClausePosition port) := by
  cases port <;> rfl

@[simp]
theorem spokeRoute_getLast? (port : Port) :
    (spokeRoute port).getLast? =
      some (variablePosition port) := by
  cases port <;> rfl

/-- The local suffix starts at its declared fan boundary point. -/
@[simp]
theorem angularFanSpokeRoute_head?
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) (index : Nat) :
    (angularFanSpokeRoute
      sourcePlacement atom index).head? =
        some
          (angularFanBoundaryPosition
            sourcePlacement atom index) := by
  simp [angularFanSpokeRoute,
    angularFanBoundaryPosition]

/-- The local suffix ends at the exact positioned semantic copy selected by
the angular-list index. -/
@[simp]
theorem angularFanSpokeRoute_getLast?
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) (index : Nat) :
    (angularFanSpokeRoute
      sourcePlacement atom index).getLast? =
        some
          (occurrenceVariablePosition sourcePlacement
            (copy atom (angularPortOfIndex index))) := by
  simp [angularFanSpokeRoute,
    occurrenceVariablePosition_copy]

/-- Every positioned local spoke suffix is an orthogonal polyline. -/
theorem angularFanSpokeRoute_orthogonal
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) (index : Nat) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (angularFanSpokeRoute
        sourcePlacement atom index) := by
  generalize portEq :
    angularPortOfIndex index = port
  cases port <;>
    simp [angularFanSpokeRoute, portEq,
      spokeRoute,
      PeriodicOrthocrossing.OrthogonalPolyline,
      Cell.add, GridSegment.IsAxisAligned,
      GridSegment.IsHorizontal, GridSegment.IsVertical]

/-- For a genuine selected index, the boundary suffix is literally the
corresponding route of the certified instantiated fan drawing. -/
theorem instantiatedAngularFanDrawing_spokeRoute
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) (count index : Nat)
    (indexLt : index < count) :
    (instantiatedAngularFanDrawing
      sourcePlacement atom count).routes index 0 =
        angularFanSpokeRoute
          sourcePlacement atom index := by
  change
    (angularFanRoutes count index 0).map
        (Cell.add (macroOrigin sourcePlacement atom)) =
      (spokeRoute (angularPortOfIndex index)).map
        (Cell.add (macroOrigin sourcePlacement atom))
  unfold angularFanRoutes
  rw [if_pos (by
      simpa only [angularFanPorts_length] using indexLt),
    if_pos rfl]
  congr 1
  rw [List.getD_eq_getElem _ _ (by
      simpa only [angularFanPorts_length] using indexLt),
    angularFanPorts_getElem count index indexLt]

/-! ## Periodically translated fan occurrences -/

/-- Physical boundary point of the same fan in the periodic occurrence
translate named by `logicalOffset`. -/
def angularFanBoundaryPositionAt
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) (logicalOffset : Cell)
    (index : Nat) : Cell :=
  Cell.add
    (angularFanBoundaryPosition
      sourcePlacement atom index)
    ((placement sourcePlacement).translation logicalOffset)

/-- Lift the certified local suffix to a neighboring periodic occurrence of
the same split-variable fan. -/
def angularFanSpokeRouteAt
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) (logicalOffset : Cell)
    (index : Nat) : List Cell :=
  (angularFanSpokeRoute
    sourcePlacement atom index).map
      (Cell.add
        ((placement sourcePlacement).translation
          logicalOffset))

/-- Translating every point of an orthogonal polyline preserves
orthogonality. -/
theorem PeriodicOrthocrossing.OrthogonalPolyline.map_add
    {points : List Cell}
    (orthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline points)
    (offset : Cell) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (points.map (Cell.add offset)) := by
  unfold PeriodicOrthocrossing.OrthogonalPolyline
    at orthogonal ⊢
  apply List.isChain_map_of_isChain
    (Cell.add offset)
  · intro first second aligned
    exact
      (GridSegment.isAxisAligned_translate
        (GridSegment.mk first second) offset).2 aligned
  · exact orthogonal

/-- The lifted suffix starts at the corresponding lifted fan boundary. -/
@[simp]
theorem angularFanSpokeRouteAt_head?
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) (logicalOffset : Cell)
    (index : Nat) :
    (angularFanSpokeRouteAt sourcePlacement
      atom logicalOffset index).head? =
        some
          (angularFanBoundaryPositionAt
            sourcePlacement atom logicalOffset index) := by
  simp [angularFanSpokeRouteAt,
    angularFanBoundaryPositionAt,
    Cell.add, add_comm]

/-- The lifted suffix ends at the selected split copy in the advertised
periodic occurrence translate. -/
@[simp]
theorem angularFanSpokeRouteAt_getLast?
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) (logicalOffset : Cell)
    (index : Nat) :
    (angularFanSpokeRouteAt sourcePlacement
      atom logicalOffset index).getLast? =
        some
          (Cell.add
            (occurrenceVariablePosition sourcePlacement
              (copy atom (angularPortOfIndex index)))
            ((placement sourcePlacement).translation
              logicalOffset)) := by
  simp [angularFanSpokeRouteAt,
    Cell.add, add_comm]

/-- Periodic lifting preserves orthogonality of every local fan suffix. -/
theorem angularFanSpokeRouteAt_orthogonal
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) (logicalOffset : Cell)
    (index : Nat) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (angularFanSpokeRouteAt sourcePlacement
        atom logicalOffset index) := by
  exact
    PeriodicOrthocrossing.OrthogonalPolyline.map_add
      (angularFanSpokeRoute_orthogonal
        sourcePlacement atom index)
      ((placement sourcePlacement).translation
        logicalOffset)

end OccurrenceSplitRing
end LeanTrominoes
