/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationCompiler
import LeanTrominoes.PeriodicThreeDMNormalizationThreeRoundDirections

/-! # Exact direction semantics of data-only normalized routes -/

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace NormalizationCompiler

open Gadget

/-- The small geometric interface needed to identify an executable final
route with its proof-free three-round direction word. -/
structure RouteDirectionConditions (input : Input)
    (edge : ContractedEdge) : Prop where
  contractedOrthogonal :
    PeriodicOrthocrossing.OrthogonalPolyline
      (contractedEdgeRoute input edge)
  firstInnerCommon :
    (trimmedMagnifiedRoute (contractedEdgeRoute input edge)).getLast? =
      (normalizationTemplateAt (normalizationTarget0 input edge)
        (firstNormalizationTemplate input (.target edge))).reverse.head?
  firstOuterCommon :
    (normalizationTemplateAt
        (normalizationPosition0 input edge.toPeriodicEdge.source)
        (firstNormalizationTemplate input (.source edge))).getLast? =
      (joinAtEndpoint
        (trimmedMagnifiedRoute (contractedEdgeRoute input edge))
        (normalizationTemplateAt (normalizationTarget0 input edge)
          (firstNormalizationTemplate input (.target edge))).reverse).head?
  firstRouteUnitSteps :
    (normalizationRoute1 input edge).IsChain
      AxisDirection.IsUnitAxisStep
  secondInnerCommon :
    (trimmedMagnifiedRoute (normalizationRoute1 input edge)).getLast? =
      (normalizationTemplateAt (normalizationTarget1 input edge)
        (secondNormalizationTemplate input (.target edge))).reverse.head?
  secondOuterCommon :
    (normalizationTemplateAt
        (normalizationPosition1 input edge.toPeriodicEdge.source)
        (secondNormalizationTemplate input (.source edge))).getLast? =
      (joinAtEndpoint
        (trimmedMagnifiedRoute (normalizationRoute1 input edge))
        (normalizationTemplateAt (normalizationTarget1 input edge)
          (secondNormalizationTemplate input (.target edge))).reverse).head?
  secondRouteUnitSteps :
    (normalizationRoute2 input edge).IsChain
      AxisDirection.IsUnitAxisStep
  finalInnerCommon :
    (trimmedMagnifiedRoute (normalizationRoute2 input edge)).getLast? =
      (normalizationTemplateAt (normalizationTarget2 input edge)
        (finalNormalizationTemplate input (.target edge))).reverse.head?
  finalOuterCommon :
    (normalizationTemplateAt
        (normalizationPosition2 input edge.toPeriodicEdge.source)
        (finalNormalizationTemplate input (.source edge))).getLast? =
      (joinAtEndpoint
        (trimmedMagnifiedRoute (normalizationRoute2 input edge))
        (normalizationTemplateAt (normalizationTarget2 input edge)
          (finalNormalizationTemplate input (.target edge))).reverse).head?
  firstSourceTemplateUnitSteps :
    (firstNormalizationTemplate input (.source edge)).IsChain
      AxisDirection.IsUnitAxisStep
  firstTargetTemplateReverseUnitSteps :
    (firstNormalizationTemplate input (.target edge)).reverse.IsChain
      AxisDirection.IsUnitAxisStep
  secondSourceTemplateUnitSteps :
    (secondNormalizationTemplate input (.source edge)).IsChain
      AxisDirection.IsUnitAxisStep
  secondTargetTemplateReverseUnitSteps :
    (secondNormalizationTemplate input (.target edge)).reverse.IsChain
      AxisDirection.IsUnitAxisStep
  finalSourceTemplateUnitSteps :
    (finalNormalizationTemplate input (.source edge)).IsChain
      AxisDirection.IsUnitAxisStep
  finalTargetTemplateReverseUnitSteps :
    (finalNormalizationTemplate input (.target edge)).reverse.IsChain
      AxisDirection.IsUnitAxisStep

/-- Proof-free finite direction word for one executable final route. -/
def finalNormalizationRouteDirections
    (input : Input) (edge : ContractedEdge) : List AxisDirection :=
  threeRoundNormalizationDirections
    (firstNormalizationTemplate input (.source edge))
    (firstNormalizationTemplate input (.target edge))
    (secondNormalizationTemplate input (.source edge))
    (secondNormalizationTemplate input (.target edge))
    (finalNormalizationTemplate input (.source edge))
    (finalNormalizationTemplate input (.target edge))
    (contractedEdgeRoute input edge)

theorem finalNormalizationRouteOffsets_eq_threeRound
    (input : Input) (edge : ContractedEdge)
    (conditions : RouteDirectionConditions input edge) :
    routeStepOffsets (finalNormalizationRoute input edge) =
      threeRoundNormalizationOffsets
        (firstNormalizationTemplate input (.source edge))
        (firstNormalizationTemplate input (.target edge))
        (secondNormalizationTemplate input (.source edge))
        (secondNormalizationTemplate input (.target edge))
        (finalNormalizationTemplate input (.source edge))
        (finalNormalizationTemplate input (.target edge))
        (contractedEdgeRoute input edge) := by
  have firstExact := routeStepOffsets_normalizeRouteWithTemplates
    (normalizationPosition0 input edge.toPeriodicEdge.source)
    (normalizationTarget0 input edge)
    (firstNormalizationTemplate input (.source edge))
    (firstNormalizationTemplate input (.target edge))
    (contractedEdgeRoute input edge)
    conditions.contractedOrthogonal conditions.firstInnerCommon
    conditions.firstOuterCommon
  have secondExact :=
    routeStepOffsets_normalizeRouteWithTemplates_of_unitSteps
      (normalizationPosition1 input edge.toPeriodicEdge.source)
      (normalizationTarget1 input edge)
      (secondNormalizationTemplate input (.source edge))
      (secondNormalizationTemplate input (.target edge))
      (normalizationRoute1 input edge)
      conditions.firstRouteUnitSteps conditions.secondInnerCommon
      conditions.secondOuterCommon
  have finalExact :=
    routeStepOffsets_normalizeRouteWithTemplates_of_unitSteps
      (normalizationPosition2 input edge.toPeriodicEdge.source)
      (normalizationTarget2 input edge)
      (finalNormalizationTemplate input (.source edge))
      (finalNormalizationTemplate input (.target edge))
      (normalizationRoute2 input edge)
      conditions.secondRouteUnitSteps conditions.finalInnerCommon
      conditions.finalOuterCommon
  rw [show routeStepOffsets (finalNormalizationRoute input edge) =
      normalizationUnitRouteOffsets
        (finalNormalizationTemplate input (.source edge))
        (finalNormalizationTemplate input (.target edge))
        (routeStepOffsets (normalizationRoute2 input edge)) by
      simpa only [finalNormalizationRoute] using finalExact]
  rw [show routeStepOffsets (normalizationRoute2 input edge) =
      normalizationUnitRouteOffsets
        (secondNormalizationTemplate input (.source edge))
        (secondNormalizationTemplate input (.target edge))
        (routeStepOffsets (normalizationRoute1 input edge)) by
      simpa only [normalizationRoute2] using secondExact]
  rw [show routeStepOffsets (normalizationRoute1 input edge) =
      normalizationRouteOffsets
        (firstNormalizationTemplate input (.source edge))
        (firstNormalizationTemplate input (.target edge))
        (contractedEdgeRoute input edge) by
      simpa only [normalizationRoute1] using firstExact]
  rfl

/-- The finite word reconstructs every exact unit offset of the executable
final route. -/
theorem map_step_finalNormalizationRouteDirections
    (input : Input) (edge : ContractedEdge)
    (conditions : RouteDirectionConditions input edge) :
    (finalNormalizationRouteDirections input edge).map
        AxisDirection.step =
      routeStepOffsets (finalNormalizationRoute input edge) := by
  rw [finalNormalizationRouteDirections]
  rw [map_step_threeRoundNormalizationDirections
    _ _ _ _ _ _ _
    conditions.firstSourceTemplateUnitSteps
    conditions.firstTargetTemplateReverseUnitSteps
    conditions.secondSourceTemplateUnitSteps
    conditions.secondTargetTemplateReverseUnitSteps
    conditions.finalSourceTemplateUnitSteps
    conditions.finalTargetTemplateReverseUnitSteps]
  exact (finalNormalizationRouteOffsets_eq_threeRound
    input edge conditions).symm

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
