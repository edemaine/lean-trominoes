/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonAdjacentVariableOuterFans
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonClauseCoordinatedFans

/-!
# Complete clause fans in adjacent ribbon macrocells

Clause outer fans are reflected, reversed variable-fan templates.  This file
checks their adjacent-macrocell contact pattern directly at the finite-table
level, together with the three interactions involving the protected local
clause gates.  The resulting complete-route theorem leaves exactly the
source-geometric obstruction: the two incoming clause directions would have
to enter their adjacent targets from the shared unit edge.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Direction-free representative of one two- or three-terminal clause-fan
shape.  Local gate geometry depends only on `hasRight`. -/
def clauseRibbonFanShape (hasRight : Bool) : ClauseRibbonFanData where
  hasRight := hasRight
  direction := fun _ => .invalid

/-- A selected variable outer template, reflected and reversed into the
clause-side orientation for one terminal shape. -/
def clauseOuterRouteFromTemplate
    (template : VariableOuterFanTemplate)
    (hasRight : Bool)
    (group : X3CClauseTerminalGroup)
    (lane : WireColor) : List Cell :=
  (template.route
      ((clauseRibbonFanShape hasRight).variableSlotForGroup group)
      lane).reverse.map ClauseRibbonFanData.reflectCell

/-- Replacing a clause fan by its direction-free shape does not change a
local gate route. -/
theorem clauseRibbonFanShape_localGateRoute
    (data : ClauseRibbonFanData)
    (group : X3CClauseTerminalGroup)
    (lane : WireColor) :
    (clauseRibbonFanShape data.hasRight).localGateRoute group lane =
      data.localGateRoute group lane := by
  rcases data with ⟨hasRight, direction⟩
  cases hasRight <;> cases group <;> cases lane <;> rfl

/-- The direction-free representative chooses the same reflected variable
slot as the original clause data. -/
@[simp]
theorem clauseRibbonFanShape_variableSlotForGroup
    (data : ClauseRibbonFanData)
    (group : X3CClauseTerminalGroup) :
    (clauseRibbonFanShape data.hasRight).variableSlotForGroup group =
      data.variableSlotForGroup group := by
  rcases data with ⟨hasRight, direction⟩
  cases hasRight <;> cases group <;> rfl

/-- Substituting the selected template in the finite helper recovers the
actual clause outer route. -/
theorem clauseOuterRouteFromTemplate_selected
    (data : ClauseRibbonFanData)
    (group : X3CClauseTerminalGroup)
    (lane : WireColor) :
    clauseOuterRouteFromTemplate
        data.reflectedOuterData.selectedTemplate data.hasRight group lane =
      data.outerRoute group lane := by
  rcases data with ⟨hasRight, direction⟩
  cases hasRight <;> cases group <;> rfl

/-- On an active group, reflecting the direction stored in the selected
variable template recovers the advertised clause incoming direction. -/
theorem ClauseRibbonFanData.selectedTemplate_reflectedDirection
    (data : ClauseRibbonFanData)
    (compatible : data.IsClockwiseCompatible)
    (group : X3CClauseTerminalGroup)
    (active : data.GroupActive group) :
    ClauseRibbonFanData.reflectedDirection
        (data.reflectedOuterData.selectedTemplate.directions.getD
          (data.variableSlotForGroup group).index .invalid) =
      data.direction group := by
  native_decide +revert

set_option maxHeartbeats 3000000

/-- Reflected clause outer routes in adjacent macrocells are contact-free
unless both incoming directions come from the shared cardinal edge. -/
theorem standardClauseOuterRoutes_strictlyAvoidEachOther_of_notFacing :
    ∀ (firstIndex secondIndex :
        Fin standardVariableOuterFanTemplates.length)
      (offsetIndex : Fin ribbonAdjacentMacrocellOffsets.length)
      firstHasRight secondHasRight firstGroup secondGroup,
      ((clauseRibbonFanShape firstHasRight).variableSlotForGroup
          firstGroup).index <
        (standardVariableOuterFanTemplates.get firstIndex).directions.length →
      ((clauseRibbonFanShape secondHasRight).variableSlotForGroup
          secondGroup).index <
        (standardVariableOuterFanTemplates.get secondIndex).directions.length →
      ∀ firstLane secondLane,
        (∀ direction, direction.IsGenuine →
          ribbonAdjacentMacrocellOffsets.get offsetIndex ≠ direction.step ∨
            ClauseRibbonFanData.reflectedDirection
                ((standardVariableOuterFanTemplates.get firstIndex).directions.getD
                  ((clauseRibbonFanShape firstHasRight).variableSlotForGroup
                    firstGroup).index .invalid) ≠ direction.opposite ∨
            ClauseRibbonFanData.reflectedDirection
                ((standardVariableOuterFanTemplates.get secondIndex).directions.getD
                  ((clauseRibbonFanShape secondHasRight).variableSlotForGroup
                    secondGroup).index .invalid) ≠ direction) →
        RoutesStrictlyAvoidEachOther
          (clauseOuterRouteFromTemplate
            (standardVariableOuterFanTemplates.get firstIndex)
            firstHasRight firstGroup firstLane)
          (translatePolyline
            (Cell.scale standardThreeStrandLayout.factor
              (ribbonAdjacentMacrocellOffsets.get offsetIndex))
            (clauseOuterRouteFromTemplate
              (standardVariableOuterFanTemplates.get secondIndex)
              secondHasRight secondGroup secondLane)) := by
  native_decide

/-- Local clause gates in adjacent macrocells are always strictly
separated. -/
theorem standardClauseLocalGateRoutes_strictlyAvoidEachOther_of_adjacent :
    ∀ (offsetIndex : Fin ribbonAdjacentMacrocellOffsets.length)
      firstHasRight secondHasRight firstGroup secondGroup
      firstLane secondLane,
      RoutesStrictlyAvoidEachOther
        ((clauseRibbonFanShape firstHasRight).localGateRoute
          firstGroup firstLane)
        (translatePolyline
          (Cell.scale standardThreeStrandLayout.factor
            (ribbonAdjacentMacrocellOffsets.get offsetIndex))
          ((clauseRibbonFanShape secondHasRight).localGateRoute
            secondGroup secondLane)) := by
  native_decide

/-- A reflected clause outer route strictly avoids every local clause gate
in an adjacent macrocell. -/
theorem standardClauseOuterRoute_strictlyAvoids_localGateRoute_of_adjacent :
    ∀ (outerIndex : Fin standardVariableOuterFanTemplates.length)
      (offsetIndex : Fin ribbonAdjacentMacrocellOffsets.length)
      outerHasRight localHasRight outerGroup localGroup,
      ((clauseRibbonFanShape outerHasRight).variableSlotForGroup
          outerGroup).index <
        (standardVariableOuterFanTemplates.get outerIndex).directions.length →
      ∀ outerLane localLane,
        RoutesStrictlyAvoidEachOther
          (clauseOuterRouteFromTemplate
            (standardVariableOuterFanTemplates.get outerIndex)
            outerHasRight outerGroup outerLane)
          (translatePolyline
            (Cell.scale standardThreeStrandLayout.factor
              (ribbonAdjacentMacrocellOffsets.get offsetIndex))
            ((clauseRibbonFanShape localHasRight).localGateRoute
              localGroup localLane)) := by
  native_decide

/-- A local clause gate strictly avoids every reflected clause outer route
in an adjacent macrocell. -/
theorem standardClauseLocalGateRoute_strictlyAvoids_outerRoute_of_adjacent :
    ∀ (outerIndex : Fin standardVariableOuterFanTemplates.length)
      (offsetIndex : Fin ribbonAdjacentMacrocellOffsets.length)
      localHasRight outerHasRight localGroup outerGroup,
      ((clauseRibbonFanShape outerHasRight).variableSlotForGroup
          outerGroup).index <
        (standardVariableOuterFanTemplates.get outerIndex).directions.length →
      ∀ localLane outerLane,
        RoutesStrictlyAvoidEachOther
          ((clauseRibbonFanShape localHasRight).localGateRoute
            localGroup localLane)
          (translatePolyline
            (Cell.scale standardThreeStrandLayout.factor
              (ribbonAdjacentMacrocellOffsets.get offsetIndex))
            (clauseOuterRouteFromTemplate
              (standardVariableOuterFanTemplates.get outerIndex)
              outerHasRight outerGroup outerLane)) := by
  native_decide

/-- Complete coordinated clause routes in adjacent standard macrocells are
strictly separated unless their source routes enter the two targets from the
shared cardinal edge. -/
theorem ClauseRibbonFanData.coordinatedRoutes_strictlyAvoidEachOther_of_adjacent_notFacing
    (firstData secondData : ClauseRibbonFanData)
    (firstCompatible : firstData.IsClockwiseCompatible)
    (secondCompatible : secondData.IsClockwiseCompatible)
    (firstGroup secondGroup : X3CClauseTerminalGroup)
    (firstActive : firstData.GroupActive firstGroup)
    (secondActive : secondData.GroupActive secondGroup)
    (firstLane secondLane : WireColor)
    (offset : Cell)
    (offsetAdjacent : RibbonMacrocellOffsetAdjacent offset)
    (notFacing : ∀ direction, direction.IsGenuine →
      offset ≠ direction.step ∨
        firstData.direction firstGroup ≠ direction.opposite ∨
        secondData.direction secondGroup ≠ direction) :
    RoutesStrictlyAvoidEachOther
      (firstData.coordinatedRoute firstGroup firstLane)
      (translatePolyline
        (Cell.scale standardThreeStrandLayout.factor offset)
        (secondData.coordinatedRoute secondGroup secondLane)) := by
  let firstOuter := firstData.reflectedOuterData
  let secondOuter := secondData.reflectedOuterData
  let firstSlot := firstData.variableSlotForGroup firstGroup
  let secondSlot := secondData.variableSlotForGroup secondGroup
  rcases List.mem_iff_get.mp
      (firstOuter.selectedTemplate_mem firstCompatible) with
    ⟨firstIndex, firstTemplateEq⟩
  rcases List.mem_iff_get.mp
      (secondOuter.selectedTemplate_mem secondCompatible) with
    ⟨secondIndex, secondTemplateEq⟩
  rcases List.mem_iff_get.mp
      ((mem_ribbonAdjacentMacrocellOffsets_iff offset).2
        offsetAdjacent) with
    ⟨offsetIndex, offsetEq⟩
  have firstSlotActive : firstOuter.SlotActive firstSlot :=
    firstData.reflectedOuterData_slotActive firstGroup firstActive
  have secondSlotActive : secondOuter.SlotActive secondSlot :=
    secondData.reflectedOuterData_slotActive secondGroup secondActive
  have firstLength :
      firstSlot.index < firstOuter.selectedTemplate.directions.length := by
    rw [firstOuter.selectedTemplate_directions firstCompatible,
      firstOuter.activeDirections_length]
    exact firstSlotActive
  have secondLength :
      secondSlot.index < secondOuter.selectedTemplate.directions.length := by
    rw [secondOuter.selectedTemplate_directions secondCompatible,
      secondOuter.activeDirections_length]
    exact secondSlotActive
  have firstIndexLength :
      ((clauseRibbonFanShape firstData.hasRight).variableSlotForGroup
          firstGroup).index <
        (standardVariableOuterFanTemplates.get firstIndex).directions.length := by
    rw [clauseRibbonFanShape_variableSlotForGroup, firstTemplateEq]
    exact firstLength
  have secondIndexLength :
      ((clauseRibbonFanShape secondData.hasRight).variableSlotForGroup
          secondGroup).index <
        (standardVariableOuterFanTemplates.get secondIndex).directions.length := by
    rw [clauseRibbonFanShape_variableSlotForGroup, secondTemplateEq]
    exact secondLength
  have firstDirection :
      ClauseRibbonFanData.reflectedDirection
          ((standardVariableOuterFanTemplates.get firstIndex).directions.getD
            ((clauseRibbonFanShape firstData.hasRight).variableSlotForGroup
              firstGroup).index .invalid) =
        firstData.direction firstGroup := by
    rw [clauseRibbonFanShape_variableSlotForGroup, firstTemplateEq]
    exact firstData.selectedTemplate_reflectedDirection
      firstCompatible firstGroup firstActive
  have secondDirection :
      ClauseRibbonFanData.reflectedDirection
          ((standardVariableOuterFanTemplates.get secondIndex).directions.getD
            ((clauseRibbonFanShape secondData.hasRight).variableSlotForGroup
              secondGroup).index .invalid) =
        secondData.direction secondGroup := by
    rw [clauseRibbonFanShape_variableSlotForGroup, secondTemplateEq]
    exact secondData.selectedTemplate_reflectedDirection
      secondCompatible secondGroup secondActive
  have outerOuter :=
    standardClauseOuterRoutes_strictlyAvoidEachOther_of_notFacing
      firstIndex secondIndex offsetIndex
      firstData.hasRight secondData.hasRight firstGroup secondGroup
      firstIndexLength secondIndexLength
      firstLane secondLane (by
        intro direction genuine
        rw [offsetEq, firstDirection, secondDirection]
        exact notFacing direction genuine)
  have outerLocal :=
    standardClauseOuterRoute_strictlyAvoids_localGateRoute_of_adjacent
      firstIndex offsetIndex firstData.hasRight secondData.hasRight
      firstGroup secondGroup
      firstIndexLength
      firstLane secondLane
  have localOuter :=
    standardClauseLocalGateRoute_strictlyAvoids_outerRoute_of_adjacent
      secondIndex offsetIndex firstData.hasRight secondData.hasRight
      firstGroup secondGroup
      secondIndexLength
      firstLane secondLane
  have localLocal :=
    standardClauseLocalGateRoutes_strictlyAvoidEachOther_of_adjacent
      offsetIndex firstData.hasRight secondData.hasRight
      firstGroup secondGroup firstLane secondLane
  rw [firstTemplateEq, secondTemplateEq, offsetEq,
    clauseOuterRouteFromTemplate_selected] at outerOuter
  rw [firstTemplateEq, offsetEq,
    clauseOuterRouteFromTemplate_selected,
    clauseRibbonFanShape_localGateRoute] at outerLocal
  rw [secondTemplateEq, offsetEq,
    clauseOuterRouteFromTemplate_selected,
    clauseRibbonFanShape_localGateRoute] at localOuter
  rw [offsetEq, clauseRibbonFanShape_localGateRoute] at localLocal
  have firstJoinedAvoidsSecondOuter :=
    outerOuter.join_left localOuter
      (firstData.outerRoute_getLast?
        firstCompatible firstGroup firstActive firstLane)
      (firstData.localGateRoute_head?
        firstGroup firstActive firstLane)
  have firstJoinedAvoidsSecondLocal :=
    outerLocal.join_left localLocal
      (firstData.outerRoute_getLast?
        firstCompatible firstGroup firstActive firstLane)
      (firstData.localGateRoute_head?
        firstGroup firstActive firstLane)
  have secondOuterLast :
      (translatePolyline
        (Cell.scale standardThreeStrandLayout.factor offset)
        (secondData.outerRoute secondGroup secondLane)).getLast? =
        some (Cell.add
          (Cell.scale standardThreeStrandLayout.factor offset)
          (secondData.outerGate secondGroup secondLane)) := by
    unfold translatePolyline
    rw [List.getLast?_map,
      secondData.outerRoute_getLast?
        secondCompatible secondGroup secondActive secondLane]
    rfl
  have secondLocalHead :
      (translatePolyline
        (Cell.scale standardThreeStrandLayout.factor offset)
        (secondData.localGateRoute secondGroup secondLane)).head? =
        some (Cell.add
          (Cell.scale standardThreeStrandLayout.factor offset)
          (secondData.outerGate secondGroup secondLane)) := by
    unfold translatePolyline
    rw [List.head?_map,
      secondData.localGateRoute_head?
        secondGroup secondActive secondLane]
    rfl
  have assembled :=
    firstJoinedAvoidsSecondOuter.join_right
      firstJoinedAvoidsSecondLocal secondOuterLast secondLocalHead
  have secondOuterRouteEq :
      clauseOuterRouteFromTemplate secondOuter.selectedTemplate
          secondData.hasRight secondGroup secondLane =
        secondData.outerRoute secondGroup secondLane := by
    simpa [secondOuter] using
      clauseOuterRouteFromTemplate_selected
        secondData secondGroup secondLane
  rw [secondOuterRouteEq] at assembled
  simpa [ClauseRibbonFanData.coordinatedRoute,
    translatePolyline, joinAtEndpoint] using assembled

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
