import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonAdjacentClauseFans
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonMacrocellStrictSeparation
import LeanTrominoes.OrthogonalPolylineTailEndpointContactSeparation

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

/-- A matching final corridor tile is ordinarily separated from the
selected clause outer route; their shared boundary point is permitted. -/
theorem matchingRibbonMacrocellRoute_avoids_standardClauseOuterRoute :
    ∀ (templateIndex : Fin standardVariableOuterFanTemplates.length)
      hasRight group,
      ((clauseRibbonFanShape hasRight).variableSlotForGroup group).index <
        (standardVariableOuterFanTemplates.get templateIndex).directions.length →
      ∀ lane incoming,
        let direction :=
          ClauseRibbonFanData.reflectedDirection
            ((standardVariableOuterFanTemplates.get templateIndex).directions.getD
              ((clauseRibbonFanShape hasRight).variableSlotForGroup
                group).index .invalid)
        incoming.IsGenuine → direction.IsGenuine →
        direction ≠ incoming.opposite →
        RoutesAvoidEachOther
          (ribbonMacrocellRoute
            direction.opposite.step incoming direction lane)
          (clauseOuterRouteFromTemplate
            (standardVariableOuterFanTemplates.get templateIndex)
            hasRight group lane) := by
  native_decide

/-- Every listed contact in the matching clause-fan interface occurs at
the tail of the final corridor tile. -/
theorem matchingRibbonMacrocellRoute_meets_standardClauseOuterRoute_onlyAtTail :
    ∀ (templateIndex : Fin standardVariableOuterFanTemplates.length)
      hasRight group,
      ((clauseRibbonFanShape hasRight).variableSlotForGroup group).index <
        (standardVariableOuterFanTemplates.get templateIndex).directions.length →
      ∀ lane incoming,
        let direction :=
          ClauseRibbonFanData.reflectedDirection
            ((standardVariableOuterFanTemplates.get templateIndex).directions.getD
              ((clauseRibbonFanShape hasRight).variableSlotForGroup
                group).index .invalid)
        incoming.IsGenuine → direction.IsGenuine →
        direction ≠ incoming.opposite →
        RoutesMeetOnlyAtFirstTail
          (ribbonMacrocellRoute
            direction.opposite.step incoming direction lane)
          (clauseOuterRouteFromTemplate
            (standardVariableOuterFanTemplates.get templateIndex)
            hasRight group lane) := by
  native_decide

/-- The exit of a tile centered one step before the standard macrocell is
the matching standard entry point. -/
theorem ribbonMacrocellExit_opposite_step_eq_standardEntry :
    ∀ direction : AxisDirection, direction.IsGenuine →
      ∀ color,
        ribbonMacrocellExit direction.opposite.step direction color =
          standardRibbonMacrocellEntry direction color := by
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

/-- A matching final corridor tile is ordinarily separated from a complete
coordinated clause fan. -/
theorem ClauseRibbonFanData.matchingRibbonMacrocellRoute_avoids_coordinatedRoute
    (data : ClauseRibbonFanData)
    (compatible : data.IsClockwiseCompatible)
    (group : X3CClauseTerminalGroup)
    (active : data.GroupActive group)
    (lane : WireColor)
    (incoming : AxisDirection)
    (incomingGenuine : incoming.IsGenuine)
    (directionGenuine : (data.direction group).IsGenuine)
    (noReverse : data.direction group ≠ incoming.opposite) :
    RoutesAvoidEachOther
      (ribbonMacrocellRoute
        (data.direction group).opposite.step incoming
        (data.direction group) lane)
      (data.coordinatedRoute group lane) := by
  let outer := data.reflectedOuterData
  let slot := data.variableSlotForGroup group
  rcases List.mem_iff_get.mp
      (outer.selectedTemplate_mem compatible) with
    ⟨templateIndex, templateEq⟩
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
  have outerAvoid :=
    matchingRibbonMacrocellRoute_avoids_standardClauseOuterRoute
      templateIndex data.hasRight group indexLength lane incoming
      incomingGenuine (by rw [selectedDirection]; exact directionGenuine)
      (by rw [selectedDirection]; exact noReverse)
  rw [selectedDirection, templateEq,
    clauseOuterRouteFromTemplate_selected] at outerAvoid
  have offsetAdjacent :
      RibbonMacrocellOffsetAdjacent (data.direction group).opposite.step := by
    cases direction : data.direction group <;>
      simp_all [RibbonMacrocellOffsetAdjacent,
        AxisDirection.IsGenuine, AxisDirection.step,
        AxisDirection.opposite]
  rcases List.mem_iff_get.mp
      ((mem_ribbonAdjacentMacrocellOffsets_iff
        (data.direction group).opposite.step).2 offsetAdjacent) with
    ⟨offsetIndex, offsetEq⟩
  have localAvoid' :=
    (standardClauseLocalGateRoute_strictlyAvoids_adjacentRibbonMacrocellRoute
      offsetIndex data.hasRight group lane incoming
      (data.direction group) lane incomingGenuine directionGenuine
      noReverse).symm
  rw [offsetEq, clauseRibbonFanShape_localGateRoute] at localAvoid'
  have assembled := outerAvoid.join_right_of_strict_suffix localAvoid'
      (data.outerRoute_getLast? compatible group active lane)
      (data.localGateRoute_head? group active lane)
  simpa [ClauseRibbonFanData.coordinatedRoute] using assembled

/-- The advertised clause entry is the only listed point shared by a final
corridor tile and its complete coordinated clause fan. -/
theorem ClauseRibbonFanData.matchingRibbonMacrocellRoute_coordinatedRoute_only_common
    (data : ClauseRibbonFanData)
    (compatible : data.IsClockwiseCompatible)
    (group : X3CClauseTerminalGroup)
    (active : data.GroupActive group)
    (lane : WireColor)
    (incoming : AxisDirection)
    (incomingGenuine : incoming.IsGenuine)
    (directionGenuine : (data.direction group).IsGenuine)
    (noReverse : data.direction group ≠ incoming.opposite) :
    ∀ point,
      point ∈ ribbonMacrocellRoute
        (data.direction group).opposite.step incoming
        (data.direction group) lane →
      point ∈ data.coordinatedRoute group lane →
      point = standardRibbonMacrocellEntry (data.direction group) lane := by
  let outer := data.reflectedOuterData
  let slot := data.variableSlotForGroup group
  rcases List.mem_iff_get.mp
      (outer.selectedTemplate_mem compatible) with
    ⟨templateIndex, templateEq⟩
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
  have outerContacts :=
    matchingRibbonMacrocellRoute_meets_standardClauseOuterRoute_onlyAtTail
      templateIndex data.hasRight group indexLength lane incoming
      incomingGenuine (by rw [selectedDirection]; exact directionGenuine)
      (by rw [selectedDirection]; exact noReverse)
  rw [selectedDirection, templateEq,
    clauseOuterRouteFromTemplate_selected] at outerContacts
  have offsetAdjacent :
      RibbonMacrocellOffsetAdjacent (data.direction group).opposite.step := by
    cases direction : data.direction group <;>
      simp_all [RibbonMacrocellOffsetAdjacent,
        AxisDirection.IsGenuine, AxisDirection.step,
        AxisDirection.opposite]
  rcases List.mem_iff_get.mp
      ((mem_ribbonAdjacentMacrocellOffsets_iff
        (data.direction group).opposite.step).2 offsetAdjacent) with
    ⟨offsetIndex, offsetEq⟩
  have localAvoid :=
    (standardClauseLocalGateRoute_strictlyAvoids_adjacentRibbonMacrocellRoute
      offsetIndex data.hasRight group lane incoming
      (data.direction group) lane incomingGenuine directionGenuine
      noReverse).symm
  rw [offsetEq, clauseRibbonFanShape_localGateRoute] at localAvoid
  intro point tileMember fanMember
  change point ∈ joinAtEndpoint
      (data.outerRoute group lane) (data.localGateRoute group lane) at fanMember
  rcases mem_joinAtEndpoint fanMember with outerMember | localMember
  · have tail := outerContacts point tileMember point outerMember rfl
    have tileLast := ribbonMacrocellRoute_getLast?
      (data.direction group).opposite.step incoming
      (data.direction group) lane
    have pointEq :
        point = ribbonMacrocellExit
          (data.direction group).opposite.step
          (data.direction group) lane :=
      Option.some.inj (tail.1.symm.trans tileLast)
    exact pointEq.trans
      (ribbonMacrocellExit_opposite_step_eq_standardEntry
        (data.direction group) directionGenuine lane)
  · exact (localAvoid.2.2.2 point tileMember point localMember rfl).elim

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
