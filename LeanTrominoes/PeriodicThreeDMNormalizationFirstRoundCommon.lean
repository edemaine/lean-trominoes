/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationRouteCommon

/-! # Common endpoints in the first normalization round -/

namespace LeanTrominoes
namespace PeriodicThreeDM

open Gadget

/-- Every certified contracted route meets its two translated Figure 2
templates at the exact endpoints required by the offset-word transform. -/
theorem ContinuousPlanarPresentation.firstNormalizationCommon
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges) :
    let planar := presentation.toPlanarPresentation
    (trimmedMagnifiedRoute (planar.contractedEdgeRoute edge)).getLast? =
        (normalizationTemplateAt (planar.normalizationTarget0 edge)
          ((ContractedEndpoint.target edge).firstNormalizationTemplate
            planar)).reverse.head? ∧
      (normalizationTemplateAt
          (planar.normalizationPosition0 edge.toPeriodicEdge.source)
          ((ContractedEndpoint.source edge).firstNormalizationTemplate
            planar)).getLast? =
        (joinAtEndpoint
          (trimmedMagnifiedRoute (planar.contractedEdgeRoute edge))
          (normalizationTemplateAt (planar.normalizationTarget0 edge)
            ((ContractedEndpoint.target edge).firstNormalizationTemplate
              planar)).reverse).head? := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  let oldRoute := planar.contractedEdgeRoute edge
  let sourceEndpoint := ContractedEndpoint.source edge
  let targetEndpoint := ContractedEndpoint.target edge
  have sourceMember : sourceEndpoint ∈ problem.contractedEndpoints := by
    simp [sourceEndpoint, contractedEndpoints, edgeMember]
  have targetMember : targetEndpoint ∈ problem.contractedEndpoints := by
    simp [targetEndpoint, contractedEndpoints, edgeMember]
  have routeLength : 2 ≤ oldRoute.length :=
    planar.contractedEdgeRoute_length_ge_two degree edgeMember
  have oldOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline oldRoute :=
    planar.contractedEdgeRoute_orthogonal_of_mem edgeMember
  obtain ⟨first, second, rest, sourceEquation⟩ :=
    List.exists_eq_cons_cons_of_length_ge_two routeLength
  obtain ⟨leading, before, last, targetEquation⟩ :=
    AxisDirection.exists_eq_append_pair_of_length_ge_two routeLength
  have endpoints :=
    planar.contractedEdgeRoute_normalizationEndpoints edgeMember
  have firstEqual : first =
      planar.normalizationPosition0 edge.toPeriodicEdge.source := by
    have oldHead := endpoints.1
    change oldRoute.head? = _ at oldHead
    rw [sourceEquation] at oldHead
    exact Option.some.inj oldHead
  have lastEqual : last = planar.normalizationTarget0 edge := by
    have oldLast := endpoints.2
    change oldRoute.getLast? = _ at oldLast
    rw [targetEquation] at oldLast
    apply Option.some.inj
    simpa using oldLast
  subst first
  subst last
  have sourceAligned :
      (GridSegment.mk
        (planar.normalizationPosition0 edge.toPeriodicEdge.source)
        second).IsAxisAligned := by
    change PeriodicOrthocrossing.OrthogonalPolyline oldRoute at oldOrthogonal
    rw [sourceEquation] at oldOrthogonal
    exact (List.isChain_cons_cons.mp oldOrthogonal).1
  have targetAligned :
      (GridSegment.mk before
        (planar.normalizationTarget0 edge)).IsAxisAligned := by
    change PeriodicOrthocrossing.OrthogonalPolyline oldRoute at oldOrthogonal
    rw [targetEquation] at oldOrthogonal
    exact (List.isChain_append_cons_cons.mp oldOrthogonal).2.1
  have sourceDirection :
      AxisDirection.between
          (planar.normalizationPosition0 edge.toPeriodicEdge.source) second =
        (sourceEndpoint.outwardSide planar).direction := by
    rw [sourceEndpoint.outwardSide_direction planar degree sourceMember]
    change AxisDirection.between
        (planar.normalizationPosition0 edge.toPeriodicEdge.source) second =
      AxisDirection.polylineFirstDirection oldRoute
    rw [sourceEquation]
    rfl
  have targetDirection :
      AxisDirection.between (planar.normalizationTarget0 edge) before =
        (targetEndpoint.outwardSide planar).direction := by
    rw [targetEndpoint.outwardSide_direction planar degree targetMember]
    change AxisDirection.between (planar.normalizationTarget0 edge) before =
      (AxisDirection.polylineLastDirection oldRoute).opposite
    rw [targetEquation]
    rw [AxisDirection.polylineLastDirection_append_pair_of_axisAligned
      leading targetAligned]
    exact AxisDirection.between_reverse_eq_opposite
      (AxisDirection.between_isGenuine_of_axisAligned targetAligned)
  have sourceUsed := sourceEndpoint.outwardSide_ne_omittedSideAt
    presentation wellFormed degree sourceMember
  have targetUsed := targetEndpoint.outwardSide_ne_omittedSideAt
    presentation wellFormed degree targetMember
  exact normalizeRouteWithTemplates_common
    (planar.normalizationPosition0 edge.toPeriodicEdge.source)
    (planar.normalizationTarget0 edge)
    (sourceEndpoint.firstNormalizationTemplate planar)
    (targetEndpoint.firstNormalizationTemplate planar)
    oldRoute
    (sourceNext := second) (targetBefore := before)
    (sourceDirection := (sourceEndpoint.outwardSide planar).direction)
    (targetDirection := (targetEndpoint.outwardSide planar).direction)
    (by rw [sourceEquation]; rfl)
    (by rw [sourceEquation]; rfl)
    (by rw [targetEquation]; simp [planar])
    (by rw [targetEquation]; simp)
    sourceAligned targetAligned sourceDirection targetDirection
    (sourceEndpoint.firstNormalizationTemplate_getLast?
      planar sourceUsed)
    (targetEndpoint.firstNormalizationTemplate_getLast?
      planar targetUsed)

end PeriodicThreeDM
end LeanTrominoes
