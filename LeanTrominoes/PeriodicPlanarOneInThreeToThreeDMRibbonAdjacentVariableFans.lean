/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonAdjacentVariableOuterFans

/-!
# Complete variable fans in adjacent ribbon macrocells

The outer-fan classifier leaves only the source-geometric case in which two
adjacent incidence directions face through their common macrocell edge.  The
local connector gates live farther inside their macrocells.  Three finite
checks show that, across an adjacent offset, local gates avoid local gates and
both local/outer cross pairs unconditionally.  Combining those checks with the
outer classifier gives the same `notFacing` interface for complete coordinated
variable stubs.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2000000

/-- Local variable-gate pieces in adjacent macrocells are always strictly
separated. -/
theorem standardVariableLocalGateRoutes_strictlyAvoidEachOther_of_adjacent :
    ∀ (offsetIndex : Fin ribbonAdjacentMacrocellOffsets.length)
      firstSlot secondSlot firstKind secondKind
      firstPolarity secondPolarity firstColor secondColor,
      RoutesStrictlyAvoidEachOther
        (standardVariableLocalGateRoute
          firstSlot firstKind firstPolarity firstColor)
        (translatePolyline
          (Cell.scale standardThreeStrandLayout.factor
            (ribbonAdjacentMacrocellOffsets.get offsetIndex))
          (standardVariableLocalGateRoute
            secondSlot secondKind secondPolarity secondColor)) := by
  native_decide

/-- A local variable-gate piece strictly avoids every selected outer-fan
piece in an adjacent macrocell. -/
theorem standardVariableLocalGateRoute_strictlyAvoids_outerRoute_of_adjacent :
    ∀ (outerIndex : Fin standardVariableOuterFanTemplates.length)
      (offsetIndex : Fin ribbonAdjacentMacrocellOffsets.length)
      localSlot outerSlot,
      outerSlot.index <
        (standardVariableOuterFanTemplates.get outerIndex).directions.length →
      ∀ kind polarity localColor outerColor,
        RoutesStrictlyAvoidEachOther
          (standardVariableLocalGateRoute
            localSlot kind polarity localColor)
          (translatePolyline
            (Cell.scale standardThreeStrandLayout.factor
              (ribbonAdjacentMacrocellOffsets.get offsetIndex))
            ((standardVariableOuterFanTemplates.get outerIndex).route
              outerSlot outerColor)) := by
  native_decide

/-- Every selected outer-fan piece strictly avoids a local variable-gate
piece in an adjacent macrocell. -/
theorem standardVariableOuterRoute_strictlyAvoids_localGateRoute_of_adjacent :
    ∀ (outerIndex : Fin standardVariableOuterFanTemplates.length)
      (offsetIndex : Fin ribbonAdjacentMacrocellOffsets.length)
      outerSlot localSlot,
      outerSlot.index <
        (standardVariableOuterFanTemplates.get outerIndex).directions.length →
      ∀ outerColor kind polarity localColor,
        RoutesStrictlyAvoidEachOther
          ((standardVariableOuterFanTemplates.get outerIndex).route
            outerSlot outerColor)
          (translatePolyline
            (Cell.scale standardThreeStrandLayout.factor
              (ribbonAdjacentMacrocellOffsets.get offsetIndex))
            (standardVariableLocalGateRoute
              localSlot kind polarity localColor)) := by
  native_decide

/-- Two complete coordinated variable-fan routes in adjacent standard
macrocells are strictly separated unless their selected incidence directions
face through the common cardinal edge. -/
theorem VariableRibbonFanData.coordinatedRoutes_strictlyAvoidEachOther_of_adjacent_notFacing
    (firstData secondData : VariableRibbonFanData)
    (firstCompatible : firstData.IsClockwiseCompatible)
    (secondCompatible : secondData.IsClockwiseCompatible)
    (firstSlot secondSlot : VariableSiteSlot)
    (firstActive : firstData.SlotActive firstSlot)
    (secondActive : secondData.SlotActive secondSlot)
    (firstColor secondColor : WireColor)
    (offset : Cell)
    (offsetAdjacent : RibbonMacrocellOffsetAdjacent offset)
    (notFacing : ∀ direction, direction.IsGenuine →
      offset ≠ direction.step ∨
        firstData.direction firstSlot ≠ direction ∨
        secondData.direction secondSlot ≠ direction.opposite) :
    RoutesStrictlyAvoidEachOther
      (firstData.coordinatedRoute firstSlot firstColor)
      (translatePolyline
        (Cell.scale standardThreeStrandLayout.factor offset)
        (secondData.coordinatedRoute secondSlot secondColor)) := by
  let firstOuter := firstData.outerData
  let secondOuter := secondData.outerData
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
  have firstLength :
      firstSlot.index < firstOuter.selectedTemplate.directions.length := by
    rw [firstOuter.selectedTemplate_directions firstCompatible,
      firstOuter.activeDirections_length]
    exact firstActive
  have secondLength :
      secondSlot.index < secondOuter.selectedTemplate.directions.length := by
    rw [secondOuter.selectedTemplate_directions secondCompatible,
      secondOuter.activeDirections_length]
    exact secondActive
  have localLocal :=
    standardVariableLocalGateRoutes_strictlyAvoidEachOther_of_adjacent
      offsetIndex firstSlot secondSlot
      (firstData.kind firstSlot) (secondData.kind secondSlot)
      (firstData.polarity firstSlot) (secondData.polarity secondSlot)
      firstColor secondColor
  have localOuter :=
    standardVariableLocalGateRoute_strictlyAvoids_outerRoute_of_adjacent
      secondIndex offsetIndex firstSlot secondSlot
      (by rw [secondTemplateEq]; exact secondLength)
      (firstData.kind firstSlot) (firstData.polarity firstSlot)
      firstColor
      ((secondData.kind secondSlot).ribbonLaneForColor secondColor)
  have outerLocal :=
    standardVariableOuterRoute_strictlyAvoids_localGateRoute_of_adjacent
      firstIndex offsetIndex firstSlot secondSlot
      (by rw [firstTemplateEq]; exact firstLength)
      ((firstData.kind firstSlot).ribbonLaneForColor firstColor)
      (secondData.kind secondSlot) (secondData.polarity secondSlot)
      secondColor
  have outerOuter :=
    firstOuter.outerRoutes_strictlyAvoidEachOther_of_adjacent_notFacing
      secondOuter firstCompatible secondCompatible
      firstSlot secondSlot firstActive secondActive
      ((firstData.kind firstSlot).ribbonLaneForColor firstColor)
      ((secondData.kind secondSlot).ribbonLaneForColor secondColor)
      offset offsetAdjacent notFacing
  rw [offsetEq] at localLocal
  rw [secondTemplateEq, offsetEq] at localOuter
  rw [firstTemplateEq, offsetEq] at outerLocal
  have firstJoinedAvoidsSecondLocal :=
    localLocal.join_left outerLocal
      (standardVariableLocalGateRoute_getLast?
        firstSlot (firstData.kind firstSlot)
        (firstData.polarity firstSlot) firstColor)
      (firstOuter.outerRoute_head?
        firstCompatible firstSlot firstActive
        ((firstData.kind firstSlot).ribbonLaneForColor firstColor))
  have firstJoinedAvoidsSecondOuter :=
    localOuter.join_left outerOuter
      (standardVariableLocalGateRoute_getLast?
        firstSlot (firstData.kind firstSlot)
        (firstData.polarity firstSlot) firstColor)
      (firstOuter.outerRoute_head?
        firstCompatible firstSlot firstActive
        ((firstData.kind firstSlot).ribbonLaneForColor firstColor))
  have secondLocalLast :
      (translatePolyline
        (Cell.scale standardThreeStrandLayout.factor offset)
        (standardVariableLocalGateRoute
          secondSlot (secondData.kind secondSlot)
          (secondData.polarity secondSlot) secondColor)).getLast? =
        some (Cell.add
          (Cell.scale standardThreeStrandLayout.factor offset)
          (standardVariableOuterGate secondSlot
            ((secondData.kind secondSlot).ribbonLaneForColor secondColor))) := by
    unfold translatePolyline
    rw [List.getLast?_map,
      standardVariableLocalGateRoute_getLast?]
    rfl
  have secondOuterHead :
      (translatePolyline
        (Cell.scale standardThreeStrandLayout.factor offset)
        (secondOuter.outerRoute secondSlot
          ((secondData.kind secondSlot).ribbonLaneForColor secondColor))).head? =
        some (Cell.add
          (Cell.scale standardThreeStrandLayout.factor offset)
          (standardVariableOuterGate secondSlot
            ((secondData.kind secondSlot).ribbonLaneForColor secondColor))) := by
    unfold translatePolyline
    rw [List.head?_map,
      secondOuter.outerRoute_head?
        secondCompatible secondSlot secondActive]
    rfl
  have assembled :=
    firstJoinedAvoidsSecondLocal.join_right
      firstJoinedAvoidsSecondOuter secondLocalLast secondOuterHead
  simpa [VariableRibbonFanData.coordinatedRoute,
    VariableOuterFanData.outerRoute,
    firstOuter, secondOuter, translatePolyline, joinAtEndpoint] using assembled

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
