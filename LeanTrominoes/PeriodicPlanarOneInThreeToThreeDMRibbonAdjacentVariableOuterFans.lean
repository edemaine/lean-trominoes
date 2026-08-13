/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonVariableCoordinatedFans

/-!
# Contacts between variable outer fans in adjacent ribbon macrocells

The coordinated outer-fan tables can approach the boundary of their owning
macrocells.  This module exhaustively classifies the only possible contact
between two such tables in neighboring macrocells: their centers must differ
by one cardinal step, and both selected source directions must point along
the shared unit edge.  Diagonal neighbors and every other direction pattern
are strictly separated.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- The eight nonzero offsets in the surrounding `3 × 3` block. -/
def ribbonAdjacentMacrocellOffsets : List Cell :=
  [(-1, -1), (-1, 0), (-1, 1),
    (0, -1), (0, 1),
    (1, -1), (1, 0), (1, 1)]

/-- The explicit eight-element list recognizes exactly the adjacent
macrocell offsets. -/
theorem mem_ribbonAdjacentMacrocellOffsets_iff (offset : Cell) :
    offset ∈ ribbonAdjacentMacrocellOffsets ↔
      RibbonMacrocellOffsetAdjacent offset := by
  rcases offset with ⟨horizontal, vertical⟩
  simp [ribbonAdjacentMacrocellOffsets,
    RibbonMacrocellOffsetAdjacent]
  omega

set_option maxHeartbeats 2000000

/-- Exhaustive coordinate certificate for two selected variable outer-fan
routes in adjacent standard macrocells.  Unless both advertised directions
traverse the shared cardinal edge, the routes have no continuous or listed
contact. -/
theorem standardVariableOuterFanRoutes_strictlyAvoidEachOther_of_notFacing :
    ∀ (firstIndex secondIndex :
        Fin standardVariableOuterFanTemplates.length)
      (offsetIndex : Fin ribbonAdjacentMacrocellOffsets.length),
      ∀ firstSlot secondSlot,
        firstSlot.index <
          (standardVariableOuterFanTemplates.get firstIndex).directions.length →
        secondSlot.index <
          (standardVariableOuterFanTemplates.get secondIndex).directions.length →
        ∀ firstColor secondColor,
          (∀ direction, direction.IsGenuine →
            ribbonAdjacentMacrocellOffsets.get offsetIndex ≠ direction.step ∨
              (standardVariableOuterFanTemplates.get firstIndex).directions.getD
                firstSlot.index .invalid ≠ direction ∨
              (standardVariableOuterFanTemplates.get secondIndex).directions.getD
                secondSlot.index .invalid ≠ direction.opposite) →
          RoutesStrictlyAvoidEachOther
            ((standardVariableOuterFanTemplates.get firstIndex).route
              firstSlot firstColor)
            (translatePolyline
              (Cell.scale standardThreeStrandLayout.factor
                (ribbonAdjacentMacrocellOffsets.get offsetIndex))
              ((standardVariableOuterFanTemplates.get secondIndex).route
                secondSlot secondColor)) := by
  native_decide

/-- Data-level form of the finite adjacent-contact classifier. -/
theorem VariableOuterFanData.outerRoutes_strictlyAvoidEachOther_of_adjacent_notFacing
    (firstData secondData : VariableOuterFanData)
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
      (firstData.outerRoute firstSlot firstColor)
      (translatePolyline
        (Cell.scale standardThreeStrandLayout.factor offset)
        (secondData.outerRoute secondSlot secondColor)) := by
  rcases List.mem_iff_get.mp
      (firstData.selectedTemplate_mem firstCompatible) with
    ⟨firstIndex, firstTemplateEq⟩
  rcases List.mem_iff_get.mp
      (secondData.selectedTemplate_mem secondCompatible) with
    ⟨secondIndex, secondTemplateEq⟩
  rcases List.mem_iff_get.mp
      ((mem_ribbonAdjacentMacrocellOffsets_iff offset).2
        offsetAdjacent) with
    ⟨offsetIndex, offsetEq⟩
  have firstLength :
      firstSlot.index < firstData.selectedTemplate.directions.length := by
    rw [firstData.selectedTemplate_directions firstCompatible,
      firstData.activeDirections_length]
    exact firstActive
  have secondLength :
      secondSlot.index < secondData.selectedTemplate.directions.length := by
    rw [secondData.selectedTemplate_directions secondCompatible,
      secondData.activeDirections_length]
    exact secondActive
  have firstDirection :
      firstData.selectedTemplate.directions.getD
          firstSlot.index .invalid =
        firstData.direction firstSlot := by
    rw [firstData.selectedTemplate_directions firstCompatible]
    exact firstData.activeDirections_getD firstSlot firstActive
  have secondDirection :
      secondData.selectedTemplate.directions.getD
          secondSlot.index .invalid =
        secondData.direction secondSlot := by
    rw [secondData.selectedTemplate_directions secondCompatible]
    exact secondData.activeDirections_getD secondSlot secondActive
  have checked :=
    standardVariableOuterFanRoutes_strictlyAvoidEachOther_of_notFacing
      firstIndex secondIndex offsetIndex firstSlot secondSlot
      (by rw [firstTemplateEq]; exact firstLength)
      (by rw [secondTemplateEq]; exact secondLength)
      firstColor secondColor
      (by
        intro direction genuine
        rw [firstTemplateEq, secondTemplateEq, offsetEq,
          firstDirection, secondDirection]
        exact notFacing direction genuine)
  rw [firstTemplateEq, secondTemplateEq, offsetEq] at checked
  exact checked

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
