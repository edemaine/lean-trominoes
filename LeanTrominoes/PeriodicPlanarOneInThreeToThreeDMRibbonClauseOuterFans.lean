import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonLaneAssignment
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonVariableOuterFans

/-!
# Clause-side outer ribbon fans

A source clause has active top and left terminal groups, and a
three-literal clause additionally has an active right group.  This file
packages their finite direction data and constructs the outer part of a
coordinated clause fan.

The construction reuses the certified variable outer-fan tables.  Reflecting
a variable fan across the vertical centerline of the standard macrocell and
reversing every route turns its variable-side exits into clause-side entries.
The active terminal order is reversed at the same time:

* a two-terminal clause uses variable slots `second, first` for `top, left`;
* a three-terminal clause uses slots `third, second, first` for
  `top, left, right`.

Thus the existing 28 cyclic direction templates supply every required
two- or three-terminal clause outer fan.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

/-- Finite data controlling one clause-side endpoint fan. -/
structure ClauseRibbonFanData where
  hasRight : Bool
  direction : X3CClauseTerminalGroup → AxisDirection
  deriving DecidableEq, Fintype

namespace ClauseRibbonFanData

/-- Active clause terminal groups, in literal order. -/
def activeGroups (data : ClauseRibbonFanData) :
    List X3CClauseTerminalGroup :=
  if data.hasRight then [.top, .left, .right] else [.top, .left]

/-- Whether one terminal group is used by the source clause. -/
def GroupActive
    (data : ClauseRibbonFanData)
    (group : X3CClauseTerminalGroup) : Prop :=
  group ∈ data.activeGroups

instance (data : ClauseRibbonFanData)
    (group : X3CClauseTerminalGroup) :
    Decidable (data.GroupActive group) := by
  unfold GroupActive
  infer_instance

/-- Reflection across the vertical centerline `x = 64`. -/
def reflectCell (point : Cell) : Cell :=
  (standardThreeStrandLayout.factor - point.1, point.2)

/-- Direction change induced by reflection and route reversal.

East and west are fixed; north and south are exchanged. -/
def reflectedDirection : AxisDirection → AxisDirection
  | .east => .east
  | .west => .west
  | .north => .south
  | .south => .north
  | .invalid => .invalid

@[simp]
theorem reflectedDirection_involution
    (direction : AxisDirection) :
    reflectedDirection (reflectedDirection direction) = direction := by
  cases direction <;> rfl

/-- Variable slot whose reflected gate is assigned to one clause group. -/
def variableSlotForGroup
    (data : ClauseRibbonFanData)
    (group : X3CClauseTerminalGroup) : VariableSiteSlot :=
  match data.hasRight, group with
  | false, .top => .second
  | false, .left => .first
  | false, .right => .first
  | true, .top => .third
  | true, .left => .second
  | true, .right => .first

/-- Clause group assigned to one active variable slot before reflection. -/
def groupForVariableSlot
    (data : ClauseRibbonFanData)
    (slot : VariableSiteSlot) : X3CClauseTerminalGroup :=
  match data.hasRight, slot with
  | false, .first => .left
  | false, .second => .top
  | false, .third => .top
  | true, .first => .right
  | true, .second => .left
  | true, .third => .top

/-- Direction-only variable fan whose reflection supplies the clause fan. -/
def reflectedOuterData
    (data : ClauseRibbonFanData) : VariableOuterFanData where
  countPred :=
    if data.hasRight then ⟨2, by decide⟩ else ⟨1, by decide⟩
  direction := fun slot =>
    reflectedDirection
      (data.direction (data.groupForVariableSlot slot))

/-- Cyclic compatibility inherited from the reflected variable fan. -/
def IsClockwiseCompatible
    (data : ClauseRibbonFanData) : Prop :=
  data.reflectedOuterData.IsClockwiseCompatible

instance (data : ClauseRibbonFanData) :
    Decidable data.IsClockwiseCompatible := by
  unfold IsClockwiseCompatible
  infer_instance

/-- Active clause groups correspond exactly to active reflected slots. -/
theorem reflectedOuterData_slotActive :
    ∀ (data : ClauseRibbonFanData) group,
      data.GroupActive group →
      data.reflectedOuterData.SlotActive
        (data.variableSlotForGroup group) := by
  native_decide

/-- Physical-lane gate obtained by reflecting a variable outer gate. -/
def outerGate
    (data : ClauseRibbonFanData)
    (group : X3CClauseTerminalGroup)
    (lane : WireColor) : Cell :=
  reflectCell
    (standardVariableOuterGate
      (data.variableSlotForGroup group) lane)

/-- Exact clause-core port occupied by one semantic color. -/
def semanticPort
    (group : X3CClauseTerminalGroup)
    (color : WireColor) : Cell :=
  Cell.add standardThreeStrandLayout.clauseOffset
    (X3CClauseOrthogonal.elementPosition
      (.terminal (terminalElementForColor color group)))

/-- Clause-core port assigned to one physical ribbon lane. -/
def lanePort
    (group : X3CClauseTerminalGroup)
    (lane : WireColor) : Cell :=
  semanticPort group
    ((variableConnectorKindForTerminal group).colorForRibbonLane lane)

/-- Assigning a semantic color to its physical lane recovers its exact
clause-core port. -/
@[simp]
theorem lanePort_ribbonLaneForColor
    (group : X3CClauseTerminalGroup)
    (color : WireColor) :
    lanePort group (clauseRibbonLaneForColor group color) =
      semanticPort group color := by
  cases group <;> cases color <;> rfl

/-- The nine physical lane ports, exposed as a compact coordinate check. -/
theorem lanePorts :
    ([(lanePort .top .red), (lanePort .top .green),
        (lanePort .top .blue)],
      [(lanePort .left .red), (lanePort .left .green),
        (lanePort .left .blue)],
      [(lanePort .right .red), (lanePort .right .green),
        (lanePort .right .blue)]) =
      ([(54, 52), (62, 52), (70, 52)],
        [(70, 76), (62, 76), (54, 76)],
        [(78, 56), (78, 64), (78, 72)]) := by
  rfl

/-- Reflected and reversed route from a physical ribbon entry to the
standardized gate of one clause group. -/
def outerRoute
    (data : ClauseRibbonFanData)
    (group : X3CClauseTerminalGroup)
    (lane : WireColor) : List Cell :=
  (data.reflectedOuterData.outerRoute
      (data.variableSlotForGroup group) lane).reverse.map reflectCell

/-- Every selected clause outer route starts at its direction-dependent
physical ribbon entry. -/
@[simp]
theorem outerRoute_head? :
    ∀ (data : ClauseRibbonFanData),
      data.IsClockwiseCompatible →
      ∀ group, data.GroupActive group →
      ∀ lane,
        (data.outerRoute group lane).head? =
          some
            (standardRibbonMacrocellEntry
              (data.direction group) lane) := by
  native_decide

/-- Every selected clause outer route ends at its reflected physical-lane
gate. -/
@[simp]
theorem outerRoute_getLast? :
    ∀ (data : ClauseRibbonFanData),
      data.IsClockwiseCompatible →
      ∀ group, data.GroupActive group →
      ∀ lane,
        (data.outerRoute group lane).getLast? =
          some (data.outerGate group lane) := by
  native_decide

/-- Every selected clause outer route is rectilinear. -/
theorem outerRoute_orthogonal :
    ∀ (data : ClauseRibbonFanData),
      data.IsClockwiseCompatible →
      ∀ group, data.GroupActive group →
      ∀ lane, OrthogonalPolyline (data.outerRoute group lane) := by
  native_decide

/-- Every point of a selected clause outer route remains in the standard
ribbon macrocell. -/
theorem outerRoute_points_bounded :
    ∀ (data : ClauseRibbonFanData),
      data.IsClockwiseCompatible →
      ∀ group, data.GroupActive group →
      ∀ lane point,
        point ∈ data.outerRoute group lane →
        InStandardRibbonMacrocell point := by
  native_decide

/-- Distinct active physical strands in one clause outer fan are strictly
separated. -/
theorem outerRoutes_strictlyAvoidEachOther :
    ∀ (data : ClauseRibbonFanData),
      data.IsClockwiseCompatible →
      ∀ firstGroup secondGroup,
        data.GroupActive firstGroup →
        data.GroupActive secondGroup →
        ∀ firstLane secondLane,
          (firstGroup, firstLane) ≠ (secondGroup, secondLane) →
          RoutesStrictlyAvoidEachOther
            (data.outerRoute firstGroup firstLane)
            (data.outerRoute secondGroup secondLane) := by
  native_decide

end ClauseRibbonFanData
end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
