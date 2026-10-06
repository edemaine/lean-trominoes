/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonAdjacentVariableFans
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonAdjacentClauseFans

/-!
# Variable and clause fans in adjacent ribbon macrocells

Mixed outer fans can contact only when the clause macrocell is the selected
first source neighbor of the variable fan.  Within that exceptional offset,
arbitrary independently selected fan templates can have additional annular
contacts; source geometry will handle it separately.  The four finite checks
below certify contact-free separation at every other adjacent offset and rule
out every contact involving a connector-local gate.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

private def mixedFanSeparationCheck (first second : List Cell) : Bool :=
  segmentBoxesSeparateCheck first second || routesStrictlyAvoidEachOtherCheck first second

private theorem mixedFanSeparationCheck_sound (first second : List Cell)
    (checked : mixedFanSeparationCheck first second = true) :
    RoutesStrictlyAvoidEachOther first second := by
  simp only [mixedFanSeparationCheck, Bool.or_eq_true] at checked
  rcases checked with boxes | exactCheck
  · exact routesStrictlyAvoidEachOther_of_segmentBoxesCheck first second boxes
  · exact (routesStrictlyAvoidEachOtherCheck_eq_true first second).mp exactCheck

/-- A selected variable outer route and reflected clause outer route in an
adjacent macrocell are contact-free unless the second center is the selected
first source neighbor of the variable route. -/
private def mixedFanCheck0 (variableIndex : Fin standardVariableOuterFanTemplates.length) : Bool :=
  finiteAll fun clauseIndex : Fin standardVariableOuterFanTemplates.length =>
      finiteAll fun offsetIndex : Fin ribbonAdjacentMacrocellOffsets.length =>
      finiteAll fun variableSlot =>
      finiteAll fun clauseHasRight =>
      finiteAll fun clauseGroup =>
      guardedCheck (variableSlot.index < (standardVariableOuterFanTemplates.get variableIndex).directions.length ∧ ((clauseRibbonFanShape clauseHasRight).variableSlotForGroup clauseGroup).index < (standardVariableOuterFanTemplates.get clauseIndex).directions.length ∧ ribbonAdjacentMacrocellOffsets.get offsetIndex ≠ ((standardVariableOuterFanTemplates.get variableIndex).directions.getD variableSlot.index .invalid).step)
        (finiteAll fun variableLane =>
      finiteAll fun clauseLane =>
      mixedFanSeparationCheck
        ((standardVariableOuterFanTemplates.get variableIndex).route
            variableSlot variableLane)
          (translatePolyline
            (Cell.scale standardThreeStrandLayout.factor
              (ribbonAdjacentMacrocellOffsets.get offsetIndex))
            (clauseOuterRouteFromTemplate
              (standardVariableOuterFanTemplates.get clauseIndex)
              clauseHasRight clauseGroup clauseLane)))

private theorem mixedFanCheck0_correct (variableIndex : Fin standardVariableOuterFanTemplates.length) :
    mixedFanCheck0 variableIndex = true := by
  fin_cases variableIndex <;> decide +kernel

theorem standardVariableClauseOuterRoutes_strictlyAvoidEachOther_of_separated :
    ∀ (variableIndex clauseIndex :
        Fin standardVariableOuterFanTemplates.length)
      (offsetIndex : Fin ribbonAdjacentMacrocellOffsets.length)
      variableSlot clauseHasRight clauseGroup,
      variableSlot.index <
        (standardVariableOuterFanTemplates.get variableIndex).directions.length →
      ((clauseRibbonFanShape clauseHasRight).variableSlotForGroup
          clauseGroup).index <
        (standardVariableOuterFanTemplates.get clauseIndex).directions.length →
      ∀ variableLane clauseLane,
        ribbonAdjacentMacrocellOffsets.get offsetIndex ≠
          ((standardVariableOuterFanTemplates.get variableIndex).directions.getD
            variableSlot.index .invalid).step →
        RoutesStrictlyAvoidEachOther
          ((standardVariableOuterFanTemplates.get variableIndex).route
            variableSlot variableLane)
          (translatePolyline
            (Cell.scale standardThreeStrandLayout.factor
              (ribbonAdjacentMacrocellOffsets.get offsetIndex))
            (clauseOuterRouteFromTemplate
              (standardVariableOuterFanTemplates.get clauseIndex)
              clauseHasRight clauseGroup clauseLane)) := by
  have checked := mixedFanCheck0_correct
  intro variableIndex clauseIndex offsetIndex variableSlot clauseHasRight clauseGroup variableActive clauseActive variableLane clauseLane notNeighbor
  simp only [mixedFanCheck0, finiteAll_eq_true, guardedCheck_eq_true] at checked
  exact mixedFanSeparationCheck_sound _ _
    (checked variableIndex clauseIndex offsetIndex variableSlot clauseHasRight clauseGroup ⟨variableActive, clauseActive, notNeighbor⟩ variableLane clauseLane)

/-- A variable local gate avoids every neighboring clause outer route. -/
private def mixedFanCheck1 (clauseIndex : Fin standardVariableOuterFanTemplates.length) : Bool :=
  finiteAll fun offsetIndex : Fin ribbonAdjacentMacrocellOffsets.length =>
      finiteAll fun variableSlot =>
      finiteAll fun clauseHasRight =>
      finiteAll fun clauseGroup =>
      guardedCheck (((clauseRibbonFanShape clauseHasRight).variableSlotForGroup clauseGroup).index < (standardVariableOuterFanTemplates.get clauseIndex).directions.length)
        (finiteAll fun variableKind =>
      finiteAll fun variablePolarity =>
      finiteAll fun variableColor =>
      finiteAll fun clauseLane =>
      mixedFanSeparationCheck
        (standardVariableLocalGateRoute
            variableSlot variableKind variablePolarity variableColor)
          (translatePolyline
            (Cell.scale standardThreeStrandLayout.factor
              (ribbonAdjacentMacrocellOffsets.get offsetIndex))
            (clauseOuterRouteFromTemplate
              (standardVariableOuterFanTemplates.get clauseIndex)
              clauseHasRight clauseGroup clauseLane)))

private theorem mixedFanCheck1_correct (clauseIndex : Fin standardVariableOuterFanTemplates.length) :
    mixedFanCheck1 clauseIndex = true := by
  fin_cases clauseIndex <;> decide +kernel

theorem standardVariableLocalGateRoute_strictlyAvoids_clauseOuterRoute_of_adjacent :
    ∀ (clauseIndex : Fin standardVariableOuterFanTemplates.length)
      (offsetIndex : Fin ribbonAdjacentMacrocellOffsets.length)
      variableSlot clauseHasRight clauseGroup,
      ((clauseRibbonFanShape clauseHasRight).variableSlotForGroup
          clauseGroup).index <
        (standardVariableOuterFanTemplates.get clauseIndex).directions.length →
      ∀ variableKind variablePolarity variableColor clauseLane,
        RoutesStrictlyAvoidEachOther
          (standardVariableLocalGateRoute
            variableSlot variableKind variablePolarity variableColor)
          (translatePolyline
            (Cell.scale standardThreeStrandLayout.factor
              (ribbonAdjacentMacrocellOffsets.get offsetIndex))
            (clauseOuterRouteFromTemplate
              (standardVariableOuterFanTemplates.get clauseIndex)
              clauseHasRight clauseGroup clauseLane)) := by
  have checked := mixedFanCheck1_correct
  intro clauseIndex offsetIndex variableSlot clauseHasRight clauseGroup active variableKind variablePolarity variableColor clauseLane
  simp only [mixedFanCheck1, finiteAll_eq_true, guardedCheck_eq_true] at checked
  exact mixedFanSeparationCheck_sound _ _
    (checked clauseIndex offsetIndex variableSlot clauseHasRight clauseGroup active variableKind variablePolarity variableColor clauseLane)

/-- A variable outer route avoids every neighboring clause local gate. -/
private def mixedFanCheck2 (variableIndex : Fin standardVariableOuterFanTemplates.length) : Bool :=
  finiteAll fun offsetIndex : Fin ribbonAdjacentMacrocellOffsets.length =>
      finiteAll fun variableSlot =>
      finiteAll fun clauseHasRight =>
      finiteAll fun clauseGroup =>
      guardedCheck (variableSlot.index < (standardVariableOuterFanTemplates.get variableIndex).directions.length)
        (finiteAll fun variableLane =>
      finiteAll fun clauseLane =>
      mixedFanSeparationCheck
        ((standardVariableOuterFanTemplates.get variableIndex).route
            variableSlot variableLane)
          (translatePolyline
            (Cell.scale standardThreeStrandLayout.factor
              (ribbonAdjacentMacrocellOffsets.get offsetIndex))
            ((clauseRibbonFanShape clauseHasRight).localGateRoute
              clauseGroup clauseLane)))

private theorem mixedFanCheck2_correct (variableIndex : Fin standardVariableOuterFanTemplates.length) :
    mixedFanCheck2 variableIndex = true := by
  fin_cases variableIndex <;> decide +kernel

theorem standardVariableOuterRoute_strictlyAvoids_clauseLocalGateRoute_of_adjacent :
    ∀ (variableIndex : Fin standardVariableOuterFanTemplates.length)
      (offsetIndex : Fin ribbonAdjacentMacrocellOffsets.length)
      variableSlot clauseHasRight clauseGroup,
      variableSlot.index <
        (standardVariableOuterFanTemplates.get variableIndex).directions.length →
      ∀ variableLane clauseLane,
        RoutesStrictlyAvoidEachOther
          ((standardVariableOuterFanTemplates.get variableIndex).route
            variableSlot variableLane)
          (translatePolyline
            (Cell.scale standardThreeStrandLayout.factor
              (ribbonAdjacentMacrocellOffsets.get offsetIndex))
            ((clauseRibbonFanShape clauseHasRight).localGateRoute
              clauseGroup clauseLane)) := by
  have checked := mixedFanCheck2_correct
  intro variableIndex offsetIndex variableSlot clauseHasRight clauseGroup active variableLane clauseLane
  simp only [mixedFanCheck2, finiteAll_eq_true, guardedCheck_eq_true] at checked
  exact mixedFanSeparationCheck_sound _ _
    (checked variableIndex offsetIndex variableSlot clauseHasRight clauseGroup active variableLane clauseLane)

/-- Variable and clause local gates in neighboring macrocells are always
contact-free. -/
private def mixedFanCheck3 (offsetIndex : Fin ribbonAdjacentMacrocellOffsets.length) : Bool :=
  finiteAll fun variableSlot =>
      finiteAll fun clauseHasRight =>
      finiteAll fun clauseGroup =>
      finiteAll fun variableKind =>
      finiteAll fun variablePolarity =>
      finiteAll fun variableColor =>
      finiteAll fun clauseLane =>
      mixedFanSeparationCheck
        (standardVariableLocalGateRoute
          variableSlot variableKind variablePolarity variableColor)
        (translatePolyline
          (Cell.scale standardThreeStrandLayout.factor
            (ribbonAdjacentMacrocellOffsets.get offsetIndex))
          ((clauseRibbonFanShape clauseHasRight).localGateRoute
            clauseGroup clauseLane))

private theorem mixedFanCheck3_correct (offsetIndex : Fin ribbonAdjacentMacrocellOffsets.length) :
    mixedFanCheck3 offsetIndex = true := by
  fin_cases offsetIndex <;> decide +kernel

theorem standardVariableLocalGateRoute_strictlyAvoids_clauseLocalGateRoute_of_adjacent :
    ∀ (offsetIndex : Fin ribbonAdjacentMacrocellOffsets.length)
      variableSlot clauseHasRight clauseGroup
      variableKind variablePolarity variableColor clauseLane,
      RoutesStrictlyAvoidEachOther
        (standardVariableLocalGateRoute
          variableSlot variableKind variablePolarity variableColor)
        (translatePolyline
          (Cell.scale standardThreeStrandLayout.factor
            (ribbonAdjacentMacrocellOffsets.get offsetIndex))
          ((clauseRibbonFanShape clauseHasRight).localGateRoute
            clauseGroup clauseLane)) := by
  have checked := mixedFanCheck3_correct
  intro offsetIndex variableSlot clauseHasRight clauseGroup variableKind variablePolarity variableColor clauseLane
  simp only [mixedFanCheck3, finiteAll_eq_true] at checked
  exact mixedFanSeparationCheck_sound _ _
    (checked offsetIndex variableSlot clauseHasRight clauseGroup variableKind variablePolarity variableColor clauseLane)

/-- Complete coordinated variable and clause routes in adjacent standard
macrocells are contact-free whenever the clause macrocell is not the selected
first source neighbor of the variable fan. -/
theorem VariableRibbonFanData.coordinatedRoute_strictlyAvoids_clauseCoordinatedRoute_of_adjacent_notFirstNeighbor
    (variableData : VariableRibbonFanData)
    (clauseData : ClauseRibbonFanData)
    (variableCompatible : variableData.IsClockwiseCompatible)
    (clauseCompatible : clauseData.IsClockwiseCompatible)
    (variableSlot : VariableSiteSlot)
    (clauseGroup : X3CClauseTerminalGroup)
    (variableActive : variableData.SlotActive variableSlot)
    (clauseActive : clauseData.GroupActive clauseGroup)
    (variableColor clauseLane : WireColor)
    (offset : Cell)
    (offsetAdjacent : RibbonMacrocellOffsetAdjacent offset)
    (notFirstNeighbor :
      offset ≠ (variableData.direction variableSlot).step) :
    RoutesStrictlyAvoidEachOther
      (variableData.coordinatedRoute variableSlot variableColor)
      (translatePolyline
        (Cell.scale standardThreeStrandLayout.factor offset)
        (clauseData.coordinatedRoute clauseGroup clauseLane)) := by
  let variableOuter := variableData.outerData
  let clauseOuter := clauseData.reflectedOuterData
  rcases List.mem_iff_get.mp
      (variableOuter.selectedTemplate_mem variableCompatible) with
    ⟨variableIndex, variableTemplateEq⟩
  rcases List.mem_iff_get.mp
      (clauseOuter.selectedTemplate_mem clauseCompatible) with
    ⟨clauseIndex, clauseTemplateEq⟩
  rcases List.mem_iff_get.mp
      ((mem_ribbonAdjacentMacrocellOffsets_iff offset).2
        offsetAdjacent) with
    ⟨offsetIndex, offsetEq⟩
  have variableLength :
      variableSlot.index <
        variableOuter.selectedTemplate.directions.length := by
    rw [variableOuter.selectedTemplate_directions variableCompatible,
      variableOuter.activeDirections_length]
    exact variableActive
  let clauseSlot := clauseData.variableSlotForGroup clauseGroup
  have clauseSlotActive : clauseOuter.SlotActive clauseSlot :=
    clauseData.reflectedOuterData_slotActive clauseGroup clauseActive
  have clauseLength :
      clauseSlot.index < clauseOuter.selectedTemplate.directions.length := by
    rw [clauseOuter.selectedTemplate_directions clauseCompatible,
      clauseOuter.activeDirections_length]
    exact clauseSlotActive
  have clauseIndexLength :
      ((clauseRibbonFanShape clauseData.hasRight).variableSlotForGroup
          clauseGroup).index <
        (standardVariableOuterFanTemplates.get clauseIndex).directions.length := by
    rw [clauseRibbonFanShape_variableSlotForGroup, clauseTemplateEq]
    exact clauseLength
  have selectedDirection :
      (standardVariableOuterFanTemplates.get variableIndex).directions.getD
          variableSlot.index .invalid =
        variableData.direction variableSlot := by
    rw [variableTemplateEq,
      variableOuter.selectedTemplate_directions variableCompatible]
    exact variableOuter.activeDirections_getD
      variableSlot variableActive
  have outerOuter :=
    standardVariableClauseOuterRoutes_strictlyAvoidEachOther_of_separated
      variableIndex clauseIndex offsetIndex
      variableSlot clauseData.hasRight clauseGroup
      (by rw [variableTemplateEq]; exact variableLength)
      clauseIndexLength
      ((variableData.kind variableSlot).ribbonLaneForColor variableColor)
      clauseLane (by
        rw [offsetEq, selectedDirection]
        exact notFirstNeighbor)
  have localOuter :=
    standardVariableLocalGateRoute_strictlyAvoids_clauseOuterRoute_of_adjacent
      clauseIndex offsetIndex variableSlot
      clauseData.hasRight clauseGroup clauseIndexLength
      (variableData.kind variableSlot)
      (variableData.polarity variableSlot)
      variableColor clauseLane
  have outerLocal :=
    standardVariableOuterRoute_strictlyAvoids_clauseLocalGateRoute_of_adjacent
      variableIndex offsetIndex variableSlot
      clauseData.hasRight clauseGroup
      (by rw [variableTemplateEq]; exact variableLength)
      ((variableData.kind variableSlot).ribbonLaneForColor variableColor)
      clauseLane
  have localLocal :=
    standardVariableLocalGateRoute_strictlyAvoids_clauseLocalGateRoute_of_adjacent
      offsetIndex variableSlot clauseData.hasRight clauseGroup
      (variableData.kind variableSlot)
      (variableData.polarity variableSlot)
      variableColor clauseLane
  rw [variableTemplateEq, clauseTemplateEq, offsetEq,
    clauseOuterRouteFromTemplate_selected] at outerOuter
  rw [clauseTemplateEq, offsetEq,
    clauseOuterRouteFromTemplate_selected] at localOuter
  rw [variableTemplateEq, offsetEq,
    clauseRibbonFanShape_localGateRoute] at outerLocal
  rw [offsetEq, clauseRibbonFanShape_localGateRoute] at localLocal
  have variableJoinedAvoidsClauseOuter :=
    localOuter.join_left outerOuter
      (standardVariableLocalGateRoute_getLast?
        variableSlot (variableData.kind variableSlot)
        (variableData.polarity variableSlot) variableColor)
      (variableOuter.outerRoute_head?
        variableCompatible variableSlot variableActive
        ((variableData.kind variableSlot).ribbonLaneForColor variableColor))
  have variableJoinedAvoidsClauseLocal :=
    localLocal.join_left outerLocal
      (standardVariableLocalGateRoute_getLast?
        variableSlot (variableData.kind variableSlot)
        (variableData.polarity variableSlot) variableColor)
      (variableOuter.outerRoute_head?
        variableCompatible variableSlot variableActive
        ((variableData.kind variableSlot).ribbonLaneForColor variableColor))
  have clauseOuterLast :
      (translatePolyline
        (Cell.scale standardThreeStrandLayout.factor offset)
        (clauseData.outerRoute clauseGroup clauseLane)).getLast? =
      some (Cell.add
        (Cell.scale standardThreeStrandLayout.factor offset)
        (clauseData.outerGate clauseGroup clauseLane)) := by
    unfold translatePolyline
    rw [List.getLast?_map,
      clauseData.outerRoute_getLast?
        clauseCompatible clauseGroup clauseActive clauseLane]
    rfl
  have clauseLocalHead :
      (translatePolyline
        (Cell.scale standardThreeStrandLayout.factor offset)
        (clauseData.localGateRoute clauseGroup clauseLane)).head? =
      some (Cell.add
        (Cell.scale standardThreeStrandLayout.factor offset)
        (clauseData.outerGate clauseGroup clauseLane)) := by
    unfold translatePolyline
    rw [List.head?_map,
      clauseData.localGateRoute_head?
        clauseGroup clauseActive clauseLane]
    rfl
  have assembled :=
    variableJoinedAvoidsClauseOuter.join_right
      variableJoinedAvoidsClauseLocal clauseOuterLast clauseLocalHead
  simpa [VariableRibbonFanData.coordinatedRoute,
    VariableOuterFanData.outerRoute,
    ClauseRibbonFanData.coordinatedRoute,
    variableOuter, clauseOuter, translatePolyline,
    joinAtEndpoint] using assembled

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
