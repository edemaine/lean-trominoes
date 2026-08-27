/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationCompiler
import LeanTrominoes.GadgetSparseRouteStepData

/-! # Proof-free starts of data-only normalized routes -/

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace NormalizationCompiler

open Gadget
open DegreeThreeVertexNormalization

theorem finalNormalizationTemplate_head?
    (input : Input) (endpoint : ContractedEndpoint) :
    (finalNormalizationTemplate input endpoint).head? = some center := by
  unfold finalNormalizationTemplate rotationRoundPortAndRoute
  split
  · exact (clockwiseRotationRoute_endpoints _).1
  · exact (identityRotationRoute_endpoints _).1

theorem normalizationTemplateAt_finalTemplate_head?
    (input : Input) (endpoint : ContractedEndpoint)
    (position : Cell) :
    (normalizationTemplateAt position
      (finalNormalizationTemplate input endpoint)).head? =
        some (normalizeVertexPosition position) := by
  simp [normalizationTemplateAt,
    PeriodicOrthocrossing.translatePolyline,
    finalNormalizationTemplate_head?, normalizeVertexPosition]

theorem finalNormalizationRoute_head?
    (input : Input) (edge : ContractedEdge) :
    (finalNormalizationRoute input edge).head? =
      some (finalNormalizationPosition input
        edge.toPeriodicEdge.source) := by
  unfold finalNormalizationRoute normalizeRouteWithTemplates
  apply joinAtEndpoint_head?
  simpa only [finalNormalizationPosition] using
    normalizationTemplateAt_finalTemplate_head?
      input (.source edge)
      (normalizationPosition2 input edge.toPeriodicEdge.source)

/-- The total cursor start of every executable final route is its affine
normalized source-vertex position. -/
theorem routeStart_finalNormalizationRoute
    (input : Input) (edge : ContractedEdge) :
    routeStart (finalNormalizationRoute input edge) =
      finalNormalizationPosition input edge.toPeriodicEdge.source := by
  have head := finalNormalizationRoute_head? input edge
  cases routeEquation : finalNormalizationRoute input edge with
  | nil => simp [routeEquation] at head
  | cons first rest =>
      rw [routeEquation] at head
      simp only [List.head?_cons, Option.some.injEq] at head
      simpa [routeStart, routeEquation] using head

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
