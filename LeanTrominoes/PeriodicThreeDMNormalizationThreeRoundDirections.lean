/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirections
import LeanTrominoes.PeriodicThreeDMNormalizationRouteDirectionTransform

/-! # The complete three-round normalization direction word -/

namespace LeanTrominoes
namespace PeriodicThreeDM

open Gadget

/-- The first round starts from the unit subdivision of the original
axis-aligned route. -/
def firstNormalizationDirections
    (sourceTemplate targetTemplate oldRoute : List Cell) :
    List AxisDirection :=
  normalizationDirectionWord sourceTemplate targetTemplate
    (unitSubdivisionDirections oldRoute)

/-- Coordinate-offset semantics of the full three-round normalization. -/
def threeRoundNormalizationOffsets
    (firstSourceTemplate firstTargetTemplate : List Cell)
    (secondSourceTemplate secondTargetTemplate : List Cell)
    (finalSourceTemplate finalTargetTemplate : List Cell)
    (oldRoute : List Cell) : List Cell :=
  normalizationUnitRouteOffsets finalSourceTemplate finalTargetTemplate
    (normalizationUnitRouteOffsets
      secondSourceTemplate secondTargetTemplate
      (normalizationRouteOffsets
        firstSourceTemplate firstTargetTemplate oldRoute))

/-- Three normalization rounds starting from an already unit-subdivided
finite direction stream. -/
def threeRoundNormalizationDirectionsFromUnitDirections
    (firstSourceTemplate firstTargetTemplate : List Cell)
    (secondSourceTemplate secondTargetTemplate : List Cell)
    (finalSourceTemplate finalTargetTemplate : List Cell)
    (oldDirections : List AxisDirection) : List AxisDirection :=
  normalizationDirectionWord finalSourceTemplate finalTargetTemplate
    (normalizationDirectionWord
      secondSourceTemplate secondTargetTemplate
      (normalizationDirectionWord
        firstSourceTemplate firstTargetTemplate oldDirections))

/-- Finite direction-word semantics of the full three-round normalization. -/
def threeRoundNormalizationDirections
    (firstSourceTemplate firstTargetTemplate : List Cell)
    (secondSourceTemplate secondTargetTemplate : List Cell)
    (finalSourceTemplate finalTargetTemplate : List Cell)
    (oldRoute : List Cell) : List AxisDirection :=
  threeRoundNormalizationDirectionsFromUnitDirections
    firstSourceTemplate firstTargetTemplate
    secondSourceTemplate secondTargetTemplate
    finalSourceTemplate finalTargetTemplate
    (unitSubdivisionDirections oldRoute)

theorem map_step_firstNormalizationDirections
    (sourceTemplate targetTemplate oldRoute : List Cell)
    (sourceUnitSteps :
      sourceTemplate.IsChain AxisDirection.IsUnitAxisStep)
    (targetReverseUnitSteps :
      targetTemplate.reverse.IsChain AxisDirection.IsUnitAxisStep) :
    (firstNormalizationDirections sourceTemplate targetTemplate
        oldRoute).map AxisDirection.step =
      normalizationRouteOffsets sourceTemplate targetTemplate oldRoute := by
  unfold firstNormalizationDirections
  rw [map_step_normalizationDirectionWord sourceTemplate targetTemplate
    (unitSubdivisionDirections oldRoute) sourceUnitSteps
    targetReverseUnitSteps]
  rw [map_step_unitSubdivisionDirections]
  rfl

/-- Under the six finite template-validity facts, mapping the complete
direction word to unit steps gives exactly the nested offset transform. -/
theorem map_step_threeRoundNormalizationDirections
    (firstSourceTemplate firstTargetTemplate : List Cell)
    (secondSourceTemplate secondTargetTemplate : List Cell)
    (finalSourceTemplate finalTargetTemplate : List Cell)
    (oldRoute : List Cell)
    (firstSourceUnitSteps :
      firstSourceTemplate.IsChain AxisDirection.IsUnitAxisStep)
    (firstTargetReverseUnitSteps :
      firstTargetTemplate.reverse.IsChain AxisDirection.IsUnitAxisStep)
    (secondSourceUnitSteps :
      secondSourceTemplate.IsChain AxisDirection.IsUnitAxisStep)
    (secondTargetReverseUnitSteps :
      secondTargetTemplate.reverse.IsChain AxisDirection.IsUnitAxisStep)
    (finalSourceUnitSteps :
      finalSourceTemplate.IsChain AxisDirection.IsUnitAxisStep)
    (finalTargetReverseUnitSteps :
      finalTargetTemplate.reverse.IsChain AxisDirection.IsUnitAxisStep) :
    (threeRoundNormalizationDirections
        firstSourceTemplate firstTargetTemplate
        secondSourceTemplate secondTargetTemplate
        finalSourceTemplate finalTargetTemplate oldRoute).map
        AxisDirection.step =
      threeRoundNormalizationOffsets
        firstSourceTemplate firstTargetTemplate
        secondSourceTemplate secondTargetTemplate
        finalSourceTemplate finalTargetTemplate oldRoute := by
  unfold threeRoundNormalizationDirections
    threeRoundNormalizationDirectionsFromUnitDirections
    threeRoundNormalizationOffsets
  rw [map_step_normalizationDirectionWord
    finalSourceTemplate finalTargetTemplate _
    finalSourceUnitSteps finalTargetReverseUnitSteps]
  rw [map_step_normalizationDirectionWord
    secondSourceTemplate secondTargetTemplate _
    secondSourceUnitSteps secondTargetReverseUnitSteps]
  rw [map_step_normalizationDirectionWord
    firstSourceTemplate firstTargetTemplate _
    firstSourceUnitSteps firstTargetReverseUnitSteps]
  rw [map_step_unitSubdivisionDirections]
  rfl

end PeriodicThreeDM
end LeanTrominoes
