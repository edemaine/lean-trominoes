import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonAdjacentClauseFans
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonMacrocellStrictSeparation

/-!
# Clause fans versus adjacent corridor macrocells

The connector-local half of a coordinated clause fan is always separated
from a legal corridor tile in a neighboring macrocell.  The selected outer
half has exactly one possible contact: a tile immediately before the clause
may leave on the fan's advertised physical-lane entry.  These finite
certificates compose across the clause fan's gate join.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2500000
set_option maxRecDepth 10000

/-- Local clause gates avoid every legal corridor tile in an adjacent
macrocell. -/
theorem standardClauseLocalGateRoute_strictlyAvoids_adjacentRibbonMacrocellRoute :
    ∀ (offsetIndex : Fin ribbonAdjacentMacrocellOffsets.length)
      hasRight group fanLane incoming outgoing tileColor,
      incoming.IsGenuine → outgoing.IsGenuine →
      outgoing ≠ incoming.opposite →
      RoutesStrictlyAvoidEachOther
        ((clauseRibbonFanShape hasRight).localGateRoute group fanLane)
        (ribbonMacrocellRoute
          (ribbonAdjacentMacrocellOffsets.get offsetIndex)
          incoming outgoing tileColor) := by
  native_decide

/-- A selected outer clause route avoids an adjacent legal corridor tile
unless the tile is immediately before the clause, leaves in the advertised
direction, and carries the same physical lane. -/
theorem standardClauseOuterRoute_strictlyAvoids_adjacentRibbonMacrocellRoute_of_separated :
    ∀ (templateIndex : Fin standardVariableOuterFanTemplates.length)
      (offsetIndex : Fin ribbonAdjacentMacrocellOffsets.length)
      hasRight group,
      ((clauseRibbonFanShape hasRight).variableSlotForGroup group).index <
        (standardVariableOuterFanTemplates.get templateIndex).directions.length →
      ∀ fanLane incoming outgoing tileColor,
        incoming.IsGenuine → outgoing.IsGenuine →
        outgoing ≠ incoming.opposite →
        ((ribbonAdjacentMacrocellOffsets.get offsetIndex ≠
              (ClauseRibbonFanData.reflectedDirection
                ((standardVariableOuterFanTemplates.get templateIndex).directions.getD
                  ((clauseRibbonFanShape hasRight).variableSlotForGroup
                    group).index .invalid)).opposite.step ∨
            outgoing =
              ClauseRibbonFanData.reflectedDirection
                ((standardVariableOuterFanTemplates.get templateIndex).directions.getD
                  ((clauseRibbonFanShape hasRight).variableSlotForGroup
                    group).index .invalid)) ∧
          (ribbonAdjacentMacrocellOffsets.get offsetIndex ≠
              (ClauseRibbonFanData.reflectedDirection
                ((standardVariableOuterFanTemplates.get templateIndex).directions.getD
                  ((clauseRibbonFanShape hasRight).variableSlotForGroup
                    group).index .invalid)).opposite.step ∨
            fanLane ≠ tileColor)) →
        RoutesStrictlyAvoidEachOther
          (clauseOuterRouteFromTemplate
            (standardVariableOuterFanTemplates.get templateIndex)
            hasRight group fanLane)
          (ribbonMacrocellRoute
            (ribbonAdjacentMacrocellOffsets.get offsetIndex)
            incoming outgoing tileColor) := by
  native_decide

/-- Complete coordinated clause fans avoid adjacent legal corridor tiles
away from the selected final source step, and also avoid that final tile
when it carries a different physical lane. -/
theorem ClauseRibbonFanData.coordinatedRoute_strictlyAvoids_adjacentRibbonMacrocellRoute_of_separated
    (data : ClauseRibbonFanData)
    (compatible : data.IsClockwiseCompatible)
    (group : X3CClauseTerminalGroup)
    (active : data.GroupActive group)
    (fanLane : WireColor)
    (offset : Cell)
    (offsetAdjacent : RibbonMacrocellOffsetAdjacent offset)
    (incoming outgoing : AxisDirection)
    (incomingGenuine : incoming.IsGenuine)
    (outgoingGenuine : outgoing.IsGenuine)
    (noReverse : outgoing ≠ incoming.opposite)
    (tileColor : WireColor)
    (separated :
      (offset ≠ (data.direction group).opposite.step ∨
        outgoing = data.direction group) ∧
      (offset ≠ (data.direction group).opposite.step ∨
        fanLane ≠ tileColor)) :
    RoutesStrictlyAvoidEachOther
      (data.coordinatedRoute group fanLane)
      (ribbonMacrocellRoute offset incoming outgoing tileColor) := by
  let outer := data.reflectedOuterData
  let slot := data.variableSlotForGroup group
  rcases List.mem_iff_get.mp
      (outer.selectedTemplate_mem compatible) with
    ⟨templateIndex, templateEq⟩
  rcases List.mem_iff_get.mp
      ((mem_ribbonAdjacentMacrocellOffsets_iff offset).2
        offsetAdjacent) with
    ⟨offsetIndex, offsetEq⟩
  have slotActive : outer.SlotActive slot :=
    data.reflectedOuterData_slotActive group active
  have routeLength :
      slot.index < outer.selectedTemplate.directions.length := by
    rw [outer.selectedTemplate_directions compatible,
      outer.activeDirections_length]
    exact slotActive
  have indexLength :
      ((clauseRibbonFanShape data.hasRight).variableSlotForGroup group).index <
        (standardVariableOuterFanTemplates.get templateIndex).directions.length := by
    rw [clauseRibbonFanShape_variableSlotForGroup, templateEq]
    exact routeLength
  have selectedDirection :
      ClauseRibbonFanData.reflectedDirection
          ((standardVariableOuterFanTemplates.get templateIndex).directions.getD
            ((clauseRibbonFanShape data.hasRight).variableSlotForGroup
              group).index .invalid) =
        data.direction group := by
    rw [clauseRibbonFanShape_variableSlotForGroup, templateEq]
    exact data.selectedTemplate_reflectedDirection compatible group active
  have localAvoid :=
    standardClauseLocalGateRoute_strictlyAvoids_adjacentRibbonMacrocellRoute
      offsetIndex data.hasRight group fanLane incoming outgoing tileColor
      incomingGenuine outgoingGenuine noReverse
  have outerAvoid :=
    standardClauseOuterRoute_strictlyAvoids_adjacentRibbonMacrocellRoute_of_separated
      templateIndex offsetIndex data.hasRight group indexLength fanLane
      incoming outgoing tileColor incomingGenuine outgoingGenuine noReverse (by
        rw [offsetEq, selectedDirection]
        exact separated)
  rw [offsetEq, clauseRibbonFanShape_localGateRoute] at localAvoid
  rw [templateEq, offsetEq,
    clauseOuterRouteFromTemplate_selected] at outerAvoid
  exact outerAvoid.join_left localAvoid
    (data.outerRoute_getLast? compatible group active fanLane)
    (data.localGateRoute_head? group active fanLane)

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
