/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeySlotData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeData

/-! # Word recipes for padded terminal carrier-key candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairCarrierKeyWordRecipes

/-- Two supported first-descriptor recipes for every neighboring translation
of one fixed affine segment. -/
def Segment.terminalCarrierKeyRecipeBlock
    (segmentIndex : Nat) (_segment : Segment) : List Recipe :=
  neighborTranslations.flatMap fun translate =>
    List.replicate 2
      { side := .first
        segmentIndex := segmentIndex
        translate := translate
        supported := true }

/-- Identical recipe blocks aligned with one segment's horizontal and
vertical classification predicates. -/
def Segment.terminalCarrierKeyRecipeBlocks
    (segmentIndex : Nat) (segment : Segment) : List (List Recipe) :=
  let block := segment.terminalCarrierKeyRecipeBlock segmentIndex
  [block, block]

/-- Terminal recipe blocks aligned with one route shape's carrier-segment
predicates. -/
def RouteShape.terminalCarrierKeyRecipeBlocks
    (shape : RouteShape) : List (List Recipe) :=
  (shape.segments .first).zipIdx.flatMap fun tagged =>
    tagged.1.terminalCarrierKeyRecipeBlocks tagged.2

/-- Complete fixed terminal recipe family aligned with
`terminalCarrierKeyActivations`. -/
def terminalCarrierKeyRecipeBlocks : List (List Recipe) :=
  allRouteShapes.flatMap RouteShape.terminalCarrierKeyRecipeBlocks

/-- Guarded terminal carrier-key words emitted from one tagged descriptor-
pair block. -/
def terminalCarrierKeyGuardedWords
    (tokens : List RouteDescriptorPairFieldTags.Token) : List (List Bool) :=
  RouteDescriptorPairCarrierKeyWordRecipes.words tokens
    (terminalCarrierKeyActivations tokens)
    terminalCarrierKeyRecipeBlocks

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
