/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingPlanarBends
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteShapeSelection

/-! # Finite affine route-bend templates -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- Three consecutive affine route points, together with the neighboring
translation and incoming segment index that identify one routed bend. -/
structure BendTemplate where
  incomingSegmentIndex : Nat
  translate : Cell
  incomingStart : Point
  bend : Point
  outgoingFinish : Point
  deriving DecidableEq

/-- Evaluate one affine bend template on one side of a semantic descriptor
pair. -/
def BendTemplate.evalPair
    (template : BendTemplate)
    (side : Side)
    (pair : RouteDescriptor × RouteDescriptor) : RouteBend where
  routeIndex := (descriptorAt pair side).edgeIndex
  incomingSegmentIndex := template.incomingSegmentIndex
  translate := template.translate
  incomingStart := template.incomingStart.evalPair pair
  bend := template.bend.evalPair pair
  outgoingFinish := template.outgoingFinish.evalPair pair

/-- Consecutive affine point triples, tagged exactly as semantic route bends. -/
def bendTemplatesAux (translate : Cell) :
    Nat → List Point → List BendTemplate
  | incomingSegmentIndex,
      incomingStart :: bend :: outgoingFinish :: rest =>
      ⟨incomingSegmentIndex, translate,
        incomingStart, bend, outgoingFinish⟩ ::
      bendTemplatesAux translate (incomingSegmentIndex + 1)
        (bend :: outgoingFinish :: rest)
  | _, _ => []

/-- All affine bend templates of one selected route shape throughout the
fixed neighboring translation block. -/
def RouteShape.bendTemplates
    (shape : RouteShape) (side : Side) : List BendTemplate :=
  neighborTranslations.flatMap fun translate =>
    bendTemplatesAux translate 0 (shape.points side)

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
