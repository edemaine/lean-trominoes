/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMVertexNormalizationRouteValidity

/-! # Common endpoints in one route-normalization round -/

namespace LeanTrominoes
namespace PeriodicThreeDM

open Gadget
open DegreeThreeVertexNormalization

/-- The endpoint geometry used by the unit-step validity proof also gives
the two exact common endpoints needed by the offset-word semantics. -/
theorem normalizeRouteWithTemplates_common
    (sourcePosition targetPosition : Cell)
    (sourceTemplate targetTemplate oldRoute : List Cell)
    {sourceNext targetBefore : Cell}
    {sourceDirection targetDirection : AxisDirection}
    (oldHead : oldRoute.head? = some sourcePosition)
    (oldSourceNext : oldRoute.tail.head? = some sourceNext)
    (oldTarget : oldRoute.getLast? = some targetPosition)
    (oldTargetBefore : oldRoute.reverse.tail.head? = some targetBefore)
    (sourceAligned :
      (GridSegment.mk sourcePosition sourceNext).IsAxisAligned)
    (targetAligned :
      (GridSegment.mk targetBefore targetPosition).IsAxisAligned)
    (sourceDirectionEq :
      AxisDirection.between sourcePosition sourceNext = sourceDirection)
    (targetDirectionEq :
      AxisDirection.between targetPosition targetBefore = targetDirection)
    (sourceLast : sourceTemplate.getLast? =
      some (Cell.add center (Cell.scale 3 sourceDirection.step)))
    (targetLast : targetTemplate.getLast? =
      some (Cell.add center (Cell.scale 3 targetDirection.step))) :
    (trimmedMagnifiedRoute oldRoute).getLast? =
        (normalizationTemplateAt targetPosition targetTemplate).reverse.head? ∧
      (normalizationTemplateAt sourcePosition sourceTemplate).getLast? =
        (joinAtEndpoint
          (trimmedMagnifiedRoute oldRoute)
          (normalizationTemplateAt
            targetPosition targetTemplate).reverse).head? := by
  have middleLast :
      (trimmedMagnifiedRoute oldRoute).getLast? =
        some (Cell.add (normalizeVertexPosition targetPosition)
          (Cell.scale 3 targetDirection.step)) := by
    rw [← targetDirectionEq]
    exact trimmedMagnifiedRoute_getLast?_of_endpoints
      oldRoute oldTarget oldTargetBefore targetAligned
  have targetHead :
      (normalizationTemplateAt targetPosition targetTemplate).reverse.head? =
        some (Cell.add (normalizeVertexPosition targetPosition)
          (Cell.scale 3 targetDirection.step)) := by
    rw [List.head?_reverse]
    exact normalizationTemplateAt_getLast?_of_three_steps
      targetPosition targetLast
  have sourceTemplateLast :
      (normalizationTemplateAt sourcePosition sourceTemplate).getLast? =
        some (Cell.add (normalizeVertexPosition sourcePosition)
          (Cell.scale 3 sourceDirection.step)) :=
    normalizationTemplateAt_getLast?_of_three_steps
      sourcePosition sourceLast
  have middleHead :
      (trimmedMagnifiedRoute oldRoute).head? =
        some (Cell.add (normalizeVertexPosition sourcePosition)
          (Cell.scale 3 sourceDirection.step)) := by
    rw [← sourceDirectionEq]
    exact trimmedMagnifiedRoute_head?_of_endpoints
      oldRoute oldHead oldSourceNext sourceAligned
  have innerHead :
      (joinAtEndpoint
          (trimmedMagnifiedRoute oldRoute)
          (normalizationTemplateAt
            targetPosition targetTemplate).reverse).head? =
        some (Cell.add (normalizeVertexPosition sourcePosition)
          (Cell.scale 3 sourceDirection.step)) :=
    joinAtEndpoint_head? middleHead
  exact ⟨middleLast.trans targetHead.symm,
    sourceTemplateLast.trans innerHead.symm⟩

end PeriodicThreeDM
end LeanTrominoes
