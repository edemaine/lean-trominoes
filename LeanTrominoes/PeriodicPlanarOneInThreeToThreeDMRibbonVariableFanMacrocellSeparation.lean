import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonAdjacentVariableFans
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonMacrocellStrictSeparation

/-!
# Variable fans versus adjacent corridor macrocells

The connector-local half of a coordinated variable fan is always separated
from a legal corridor tile in a neighboring macrocell.  The selected outer
half has exactly one possible contact: its advertised physical-lane exit may
meet the same lane entering the tile one source step later.  These finite
certificates compose across the variable fan's gate join.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2500000
set_option maxRecDepth 10000

/-- Local connector gates avoid every legal corridor tile in an adjacent
macrocell. -/
theorem standardVariableLocalGateRoute_strictlyAvoids_adjacentRibbonMacrocellRoute :
    ∀ (offsetIndex : Fin ribbonAdjacentMacrocellOffsets.length)
      slot kind polarity fanColor incoming outgoing tileColor,
      incoming.IsGenuine → outgoing.IsGenuine →
      outgoing ≠ incoming.opposite →
      RoutesStrictlyAvoidEachOther
        (standardVariableLocalGateRoute slot kind polarity fanColor)
        (ribbonMacrocellRoute
          (ribbonAdjacentMacrocellOffsets.get offsetIndex)
          incoming outgoing tileColor) := by
  native_decide

/-- A selected outer variable route avoids an adjacent legal corridor tile
when it is not one source step in the selected direction, or when it is that
first tile but enters on a different physical lane.  The legal-turn premise
rules out the reverse-facing tile exit in the latter case. -/
theorem standardVariableOuterRoute_strictlyAvoids_adjacentRibbonMacrocellRoute_of_separated :
    ∀ (templateIndex : Fin standardVariableOuterFanTemplates.length)
      (offsetIndex : Fin ribbonAdjacentMacrocellOffsets.length)
      slot,
      slot.index <
        (standardVariableOuterFanTemplates.get templateIndex).directions.length →
      ∀ fanLane incoming outgoing tileColor,
        incoming.IsGenuine → outgoing.IsGenuine →
        outgoing ≠ incoming.opposite →
        ((ribbonAdjacentMacrocellOffsets.get offsetIndex ≠
              ((standardVariableOuterFanTemplates.get templateIndex).directions.getD
                slot.index .invalid).step ∨
            incoming =
              (standardVariableOuterFanTemplates.get templateIndex).directions.getD
                slot.index .invalid) ∧
          (ribbonAdjacentMacrocellOffsets.get offsetIndex ≠
              ((standardVariableOuterFanTemplates.get templateIndex).directions.getD
                slot.index .invalid).step ∨
            fanLane ≠ tileColor)) →
        RoutesStrictlyAvoidEachOther
          ((standardVariableOuterFanTemplates.get templateIndex).route
            slot fanLane)
          (ribbonMacrocellRoute
            (ribbonAdjacentMacrocellOffsets.get offsetIndex)
            incoming outgoing tileColor) := by
  native_decide

/-- Complete coordinated variable fans avoid adjacent legal corridor tiles
away from their selected first source step, and also avoid the first tile
when it enters on a different physical lane. -/
theorem VariableRibbonFanData.coordinatedRoute_strictlyAvoids_adjacentRibbonMacrocellRoute_of_separated
    (data : VariableRibbonFanData)
    (compatible : data.IsClockwiseCompatible)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (color : WireColor)
    (offset : Cell)
    (offsetAdjacent : RibbonMacrocellOffsetAdjacent offset)
    (incoming outgoing : AxisDirection)
    (incomingGenuine : incoming.IsGenuine)
    (outgoingGenuine : outgoing.IsGenuine)
    (noReverse : outgoing ≠ incoming.opposite)
    (tileColor : WireColor)
    (separated :
      (offset ≠ (data.direction slot).step ∨
        incoming = data.direction slot) ∧
      (offset ≠ (data.direction slot).step ∨
        (data.kind slot).ribbonLaneForColor color ≠ tileColor)) :
    RoutesStrictlyAvoidEachOther
      (data.coordinatedRoute slot color)
      (ribbonMacrocellRoute offset incoming outgoing tileColor) := by
  let outer := data.outerData
  rcases List.mem_iff_get.mp
      (outer.selectedTemplate_mem compatible) with
    ⟨templateIndex, templateEq⟩
  rcases List.mem_iff_get.mp
      ((mem_ribbonAdjacentMacrocellOffsets_iff offset).2
        offsetAdjacent) with
    ⟨offsetIndex, offsetEq⟩
  have routeLength :
      slot.index < outer.selectedTemplate.directions.length := by
    rw [outer.selectedTemplate_directions compatible,
      outer.activeDirections_length]
    exact active
  have selectedDirection :
      outer.selectedTemplate.directions.getD slot.index .invalid =
        data.direction slot := by
    rw [outer.selectedTemplate_directions compatible]
    exact outer.activeDirections_getD slot active
  have localAvoid :=
    standardVariableLocalGateRoute_strictlyAvoids_adjacentRibbonMacrocellRoute
      offsetIndex slot (data.kind slot) (data.polarity slot) color
      incoming outgoing tileColor
      incomingGenuine outgoingGenuine noReverse
  have outerAvoid :=
    standardVariableOuterRoute_strictlyAvoids_adjacentRibbonMacrocellRoute_of_separated
      templateIndex offsetIndex slot
      (by rw [templateEq]; exact routeLength)
      ((data.kind slot).ribbonLaneForColor color)
      incoming outgoing tileColor
      incomingGenuine outgoingGenuine noReverse (by
        rw [templateEq, offsetEq, selectedDirection]
        exact separated)
  rw [offsetEq] at localAvoid
  rw [templateEq, offsetEq] at outerAvoid
  exact localAvoid.join_left outerAvoid
    (standardVariableLocalGateRoute_getLast?
      slot (data.kind slot) (data.polarity slot) color)
    (outer.outerRoute_head? compatible slot active
      ((data.kind slot).ribbonLaneForColor color))

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
