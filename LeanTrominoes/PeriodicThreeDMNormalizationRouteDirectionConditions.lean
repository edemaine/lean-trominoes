/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationCompilerRouteDirections
import LeanTrominoes.PeriodicThreeDMNormalizationFirstRoundCommon
import LeanTrominoes.PeriodicThreeDMNormalizationCyclicRoundCommon

/-! # Route-direction conditions from a certified presentation -/

namespace LeanTrominoes
namespace PeriodicThreeDM

open Gadget

/-- A continuously planar presentation supplies every geometric condition
needed to identify the data-only final route with its finite direction word. -/
theorem ContinuousPlanarPresentation.routeDirectionConditions
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges) :
    NormalizationCompiler.RouteDirectionConditions
      (NormalizationCompiler.inputOfPresentation
        presentation.toPlanarPresentation) edge := by
  let planar := presentation.toPlanarPresentation
  have firstCommon := presentation.firstNormalizationCommon
    wellFormed degree edgeMember
  have secondCommon := presentation.secondNormalizationCommon
    degree edgeMember
  have finalCommon := presentation.finalNormalizationCommon
    wellFormed degree edgeMember
  refine
    { contractedOrthogonal := ?_
      firstInnerCommon := ?_
      firstOuterCommon := ?_
      firstRouteUnitSteps := ?_
      secondInnerCommon := ?_
      secondOuterCommon := ?_
      secondRouteUnitSteps := ?_
      finalInnerCommon := ?_
      finalOuterCommon := ?_ }
  · change PeriodicOrthocrossing.OrthogonalPolyline
      (planar.contractedEdgeRoute edge)
    exact planar.contractedEdgeRoute_orthogonal_of_mem edgeMember
  · change
      (trimmedMagnifiedRoute (planar.contractedEdgeRoute edge)).getLast? =
        (normalizationTemplateAt (planar.normalizationTarget0 edge)
          ((ContractedEndpoint.target edge).firstNormalizationTemplate
            planar)).reverse.head?
    exact firstCommon.1
  · change
      (normalizationTemplateAt
          (planar.normalizationPosition0 edge.toPeriodicEdge.source)
          ((ContractedEndpoint.source edge).firstNormalizationTemplate
            planar)).getLast? =
        (joinAtEndpoint
          (trimmedMagnifiedRoute (planar.contractedEdgeRoute edge))
          (normalizationTemplateAt (planar.normalizationTarget0 edge)
            ((ContractedEndpoint.target edge).firstNormalizationTemplate
              planar)).reverse).head?
    exact firstCommon.2
  · change (planar.normalizationRoute1 edge).IsChain
      AxisDirection.IsUnitAxisStep
    exact presentation.normalizationRoute1_unitSteps
      wellFormed degree edgeMember
  · change
      (trimmedMagnifiedRoute (planar.normalizationRoute1 edge)).getLast? =
        (normalizationTemplateAt (planar.normalizationTarget1 edge)
          ((ContractedEndpoint.target edge).secondNormalizationTemplate
            planar)).reverse.head?
    exact secondCommon.1
  · change
      (normalizationTemplateAt
          (planar.normalizationPosition1 edge.toPeriodicEdge.source)
          ((ContractedEndpoint.source edge).secondNormalizationTemplate
            planar)).getLast? =
        (joinAtEndpoint
          (trimmedMagnifiedRoute (planar.normalizationRoute1 edge))
          (normalizationTemplateAt (planar.normalizationTarget1 edge)
            ((ContractedEndpoint.target edge).secondNormalizationTemplate
              planar)).reverse).head?
    exact secondCommon.2
  · change (planar.normalizationRoute2 edge).IsChain
      AxisDirection.IsUnitAxisStep
    exact presentation.normalizationRoute2_unitSteps
      wellFormed degree edgeMember
  · change
      (trimmedMagnifiedRoute (planar.normalizationRoute2 edge)).getLast? =
        (normalizationTemplateAt (planar.normalizationTarget2 edge)
          ((ContractedEndpoint.target edge).finalNormalizationTemplate
            planar)).reverse.head?
    exact finalCommon.1
  · change
      (normalizationTemplateAt
          (planar.normalizationPosition2 edge.toPeriodicEdge.source)
          ((ContractedEndpoint.source edge).finalNormalizationTemplate
            planar)).getLast? =
        (joinAtEndpoint
          (trimmedMagnifiedRoute (planar.normalizationRoute2 edge))
          (normalizationTemplateAt (planar.normalizationTarget2 edge)
            ((ContractedEndpoint.target edge).finalNormalizationTemplate
              planar)).reverse).head?
    exact finalCommon.2

end PeriodicThreeDM
end LeanTrominoes
