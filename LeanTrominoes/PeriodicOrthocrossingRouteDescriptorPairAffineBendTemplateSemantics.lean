/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineBendTemplateData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteShapeSegmentSemantics

/-! # Exact semantics of finite affine route-bend templates -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- Evaluating consecutive affine triples commutes with semantic bend
enumeration. -/
theorem bendTemplatesAux_map_evalPair
    (translate : Cell) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor) :
    ∀ (points : List Point) (incomingSegmentIndex : Nat),
      (bendTemplatesAux translate incomingSegmentIndex points).map
          (fun template => template.evalPair side pair) =
        routeBendsAux (descriptorAt pair side).edgeIndex translate
          incomingSegmentIndex
          (points.map fun point => point.evalPair pair) := by
  intro points
  induction points with
  | nil =>
      intro incomingSegmentIndex
      rfl
  | cons first rest induction =>
      cases rest with
      | nil =>
          intro incomingSegmentIndex
          rfl
      | cons second rest =>
          cases rest with
          | nil =>
              intro incomingSegmentIndex
              rfl
          | cons third rest =>
              intro incomingSegmentIndex
              simp only [bendTemplatesAux, List.map_cons, routeBendsAux]
              rw [induction]
              rfl

/-- A matching finite route shape evaluates to exactly the semantic bends of
that descriptor throughout the neighboring translation block. -/
theorem RouteShape.map_evalPair_bendTemplates
    (shape : RouteShape) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor)
    (shapeMatches : shape.Matches (descriptorAt pair side)) :
    (shape.bendTemplates side).map
        (fun template => template.evalPair side pair) =
      neighborTranslations.flatMap fun translate =>
        routeBends (descriptorAt pair side).edgeIndex translate
          (descriptorAt pair side).route := by
  unfold RouteShape.bendTemplates
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro translate _
  rw [bendTemplatesAux_map_evalPair]
  unfold routeBends
  rw [shape.map_evalPair_points side pair shapeMatches]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
