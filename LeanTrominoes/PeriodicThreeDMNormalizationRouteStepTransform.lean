/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteStepJoin
import LeanTrominoes.PeriodicThreeDMNormalizationTrimmedRouteSteps

/-! # One-round normalization as an exact offset-word transform -/

namespace LeanTrominoes
namespace PeriodicThreeDM

open Gadget

/-- Positioning a finite normalization template does not change its offsets. -/
@[simp]
theorem routeStepOffsets_normalizationTemplateAt
    (position : Cell) (template : List Cell) :
    routeStepOffsets (normalizationTemplateAt position template) =
      routeStepOffsets template := by
  unfold normalizationTemplateAt
  exact routeStepOffsets_translatePolyline _ _

/-- The same translation invariance holds after traversing a target template
in reverse. -/
@[simp]
theorem routeStepOffsets_normalizationTemplateAt_reverse
    (position : Cell) (template : List Cell) :
    routeStepOffsets (normalizationTemplateAt position template).reverse =
      routeStepOffsets template.reverse := by
  unfold normalizationTemplateAt
  unfold PeriodicOrthocrossing.translatePolyline
  rw [← List.map_reverse]
  exact routeStepOffsets_translatePolyline _ _

/-- Proof-free offset transform performed by one normalization round. -/
def normalizationRouteOffsets
    (sourceTemplate targetTemplate oldRoute : List Cell) : List Cell :=
  routeStepOffsets sourceTemplate ++
    (trimThreeOffsets
        (repeatTwelveOffsets (unitSubdivisionOffsets oldRoute)) ++
      routeStepOffsets targetTemplate.reverse)

/-- With the two advertised common endpoints, the cell-level normalizer
realizes exactly `normalizationRouteOffsets`. -/
theorem routeStepOffsets_normalizeRouteWithTemplates
    (sourcePosition targetPosition : Cell)
    (sourceTemplate targetTemplate oldRoute : List Cell)
    (orthogonal : PeriodicOrthocrossing.OrthogonalPolyline oldRoute)
    (innerCommon :
      (trimmedMagnifiedRoute oldRoute).getLast? =
        (normalizationTemplateAt targetPosition targetTemplate).reverse.head?)
    (outerCommon :
      (normalizationTemplateAt sourcePosition sourceTemplate).getLast? =
        (joinAtEndpoint
          (trimmedMagnifiedRoute oldRoute)
          (normalizationTemplateAt
            targetPosition targetTemplate).reverse).head?) :
    routeStepOffsets
        (normalizeRouteWithTemplates sourcePosition targetPosition
          sourceTemplate targetTemplate oldRoute) =
      normalizationRouteOffsets sourceTemplate targetTemplate oldRoute := by
  unfold normalizeRouteWithTemplates
  rw [routeStepOffsets_joinAtEndpoint _ _ outerCommon]
  rw [routeStepOffsets_joinAtEndpoint _ _ innerCommon]
  rw [routeStepOffsets_normalizationTemplateAt,
    routeStepOffsets_normalizationTemplateAt_reverse,
    routeStepOffsets_trimmedMagnifiedRoute oldRoute orthogonal]
  rfl

/-- Unit-route form used by the second and third normalization rounds. -/
def normalizationUnitRouteOffsets
    (sourceTemplate targetTemplate : List Cell)
    (oldOffsets : List Cell) : List Cell :=
  routeStepOffsets sourceTemplate ++
    (trimThreeOffsets (repeatTwelveOffsets oldOffsets) ++
      routeStepOffsets targetTemplate.reverse)

theorem routeStepOffsets_normalizeRouteWithTemplates_of_unitSteps
    (sourcePosition targetPosition : Cell)
    (sourceTemplate targetTemplate oldRoute : List Cell)
    (unitSteps : oldRoute.IsChain AxisDirection.IsUnitAxisStep)
    (innerCommon :
      (trimmedMagnifiedRoute oldRoute).getLast? =
        (normalizationTemplateAt targetPosition targetTemplate).reverse.head?)
    (outerCommon :
      (normalizationTemplateAt sourcePosition sourceTemplate).getLast? =
        (joinAtEndpoint
          (trimmedMagnifiedRoute oldRoute)
          (normalizationTemplateAt
            targetPosition targetTemplate).reverse).head?) :
    routeStepOffsets
        (normalizeRouteWithTemplates sourcePosition targetPosition
          sourceTemplate targetTemplate oldRoute) =
      normalizationUnitRouteOffsets sourceTemplate targetTemplate
        (routeStepOffsets oldRoute) := by
  have orthogonal : PeriodicOrthocrossing.OrthogonalPolyline oldRoute :=
    unitSteps.imp fun _ _ unit =>
      AxisDirection.isAxisAligned_of_between_isGenuine
        (AxisDirection.between_isGenuine_of_unitAxisStep unit)
  rw [routeStepOffsets_normalizeRouteWithTemplates
    sourcePosition targetPosition sourceTemplate targetTemplate oldRoute
    orthogonal innerCommon outerCommon]
  unfold normalizationRouteOffsets normalizationUnitRouteOffsets
  rw [unitSubdivisionOffsets_eq_routeStepOffsets oldRoute unitSteps]

end PeriodicThreeDM
end LeanTrominoes
