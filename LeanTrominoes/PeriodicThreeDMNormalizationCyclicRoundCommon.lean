/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationRouteCommon

/-! # Common endpoints in the cyclic normalization rounds -/

namespace LeanTrominoes
namespace PeriodicThreeDM

open Gadget

/-- The first cyclic replacement meets the route produced by the Figure 2
round at both advertised common endpoints. -/
theorem ContinuousPlanarPresentation.secondNormalizationCommon
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges) :
    let planar := presentation.toPlanarPresentation
    (trimmedMagnifiedRoute (planar.normalizationRoute1 edge)).getLast? =
        (normalizationTemplateAt (planar.normalizationTarget1 edge)
          ((ContractedEndpoint.target edge).secondNormalizationTemplate
            planar)).reverse.head? ∧
      (normalizationTemplateAt
          (planar.normalizationPosition1 edge.toPeriodicEdge.source)
          ((ContractedEndpoint.source edge).secondNormalizationTemplate
            planar)).getLast? =
        (joinAtEndpoint
          (trimmedMagnifiedRoute (planar.normalizationRoute1 edge))
          (normalizationTemplateAt (planar.normalizationTarget1 edge)
            ((ContractedEndpoint.target edge).secondNormalizationTemplate
              planar)).reverse).head? := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  let sourceEndpoint := ContractedEndpoint.source edge
  let targetEndpoint := ContractedEndpoint.target edge
  let sourcePort := sourceEndpoint.firstNormalizedPort planar
  let targetPort := targetEndpoint.firstNormalizedPort planar
  have endpoints := presentation.normalizationRoute1_endpointGeometry
    degree edgeMember
  have sourceStep : AxisDirection.IsUnitAxisStep
      (planar.normalizationPosition1 edge.toPeriodicEdge.source)
      (Cell.add
        (planar.normalizationPosition1 edge.toPeriodicEdge.source)
        sourcePort.direction.step) :=
    ⟨sourcePort.direction,
      CanonicalVertexPort.direction_isGenuine sourcePort, rfl⟩
  have targetStep : AxisDirection.IsUnitAxisStep
      (planar.normalizationTarget1 edge)
      (Cell.add (planar.normalizationTarget1 edge)
        targetPort.direction.step) :=
    ⟨targetPort.direction,
      CanonicalVertexPort.direction_isGenuine targetPort, rfl⟩
  exact normalizeRouteWithTemplates_common
    (planar.normalizationPosition1 edge.toPeriodicEdge.source)
    (planar.normalizationTarget1 edge)
    (sourceEndpoint.secondNormalizationTemplate planar)
    (targetEndpoint.secondNormalizationTemplate planar)
    (planar.normalizationRoute1 edge)
    (sourceNext := Cell.add
      (planar.normalizationPosition1 edge.toPeriodicEdge.source)
      sourcePort.direction.step)
    (targetBefore := Cell.add (planar.normalizationTarget1 edge)
      targetPort.direction.step)
    (sourceDirection := sourcePort.direction)
    (targetDirection := targetPort.direction)
    endpoints.1 endpoints.2.1 endpoints.2.2.1 endpoints.2.2.2
    sourceStep.isAxisAligned targetStep.symm.isAxisAligned
    (AxisDirection.between_add_step _
      (CanonicalVertexPort.direction_isGenuine sourcePort))
    (AxisDirection.between_add_step _
      (CanonicalVertexPort.direction_isGenuine targetPort))
    (sourceEndpoint.secondNormalizationTemplate_getLast? planar)
    (targetEndpoint.secondNormalizationTemplate_getLast? planar)

/-- The final cyclic replacement likewise meets the second-round route at
both advertised common endpoints. -/
theorem ContinuousPlanarPresentation.finalNormalizationCommon
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges) :
    let planar := presentation.toPlanarPresentation
    (trimmedMagnifiedRoute (planar.normalizationRoute2 edge)).getLast? =
        (normalizationTemplateAt (planar.normalizationTarget2 edge)
          ((ContractedEndpoint.target edge).finalNormalizationTemplate
            planar)).reverse.head? ∧
      (normalizationTemplateAt
          (planar.normalizationPosition2 edge.toPeriodicEdge.source)
          ((ContractedEndpoint.source edge).finalNormalizationTemplate
            planar)).getLast? =
        (joinAtEndpoint
          (trimmedMagnifiedRoute (planar.normalizationRoute2 edge))
          (normalizationTemplateAt (planar.normalizationTarget2 edge)
            ((ContractedEndpoint.target edge).finalNormalizationTemplate
              planar)).reverse).head? := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  let sourceEndpoint := ContractedEndpoint.source edge
  let targetEndpoint := ContractedEndpoint.target edge
  let sourcePort := sourceEndpoint.secondNormalizedPort planar
  let targetPort := targetEndpoint.secondNormalizedPort planar
  have endpoints := presentation.normalizationRoute2_endpointGeometry
    wellFormed degree edgeMember
  have sourceStep : AxisDirection.IsUnitAxisStep
      (planar.normalizationPosition2 edge.toPeriodicEdge.source)
      (Cell.add
        (planar.normalizationPosition2 edge.toPeriodicEdge.source)
        sourcePort.direction.step) :=
    ⟨sourcePort.direction,
      CanonicalVertexPort.direction_isGenuine sourcePort, rfl⟩
  have targetStep : AxisDirection.IsUnitAxisStep
      (planar.normalizationTarget2 edge)
      (Cell.add (planar.normalizationTarget2 edge)
        targetPort.direction.step) :=
    ⟨targetPort.direction,
      CanonicalVertexPort.direction_isGenuine targetPort, rfl⟩
  exact normalizeRouteWithTemplates_common
    (planar.normalizationPosition2 edge.toPeriodicEdge.source)
    (planar.normalizationTarget2 edge)
    (sourceEndpoint.finalNormalizationTemplate planar)
    (targetEndpoint.finalNormalizationTemplate planar)
    (planar.normalizationRoute2 edge)
    (sourceNext := Cell.add
      (planar.normalizationPosition2 edge.toPeriodicEdge.source)
      sourcePort.direction.step)
    (targetBefore := Cell.add (planar.normalizationTarget2 edge)
      targetPort.direction.step)
    (sourceDirection := sourcePort.direction)
    (targetDirection := targetPort.direction)
    endpoints.1 endpoints.2.1 endpoints.2.2.1 endpoints.2.2.2
    sourceStep.isAxisAligned targetStep.symm.isAxisAligned
    (AxisDirection.between_add_step _
      (CanonicalVertexPort.direction_isGenuine sourcePort))
    (AxisDirection.between_add_step _
      (CanonicalVertexPort.direction_isGenuine targetPort))
    (sourceEndpoint.finalNormalizationTemplate_getLast? planar)
    (targetEndpoint.finalNormalizationTemplate_getLast? planar)

end PeriodicThreeDM
end LeanTrominoes
