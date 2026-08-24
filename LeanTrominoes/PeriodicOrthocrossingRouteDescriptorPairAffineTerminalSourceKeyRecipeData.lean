/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyTagData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyWordRecipeData

/-! # Doubled source-key recipes for padded terminal nodes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open CarrierNodeSourceKeys
open RouteDescriptorPairCarrierKeyWordRecipes

def terminalSourceKeyRecipe
    (segmentIndex : Nat) (translate : Cell) (endpoint : SegmentEnd) :
    Recipe :=
  { side := .first
    segmentIndex := 8 * segmentIndex + segmentEndTag endpoint
    translate := translate
    supported := true }

/-- Two component recipes for each of the two terminal-node slots of every
neighboring occurrence. -/
def Segment.terminalSourceKeyRecipeBlock
    (segmentIndex : Nat) (_segment : Segment) : List Recipe :=
  neighborTranslations.flatMap fun translate =>
    let start := terminalSourceKeyRecipe segmentIndex translate .start
    let finish := terminalSourceKeyRecipe segmentIndex translate .finish
    [start, start, finish, finish]

def Segment.terminalSourceKeyRecipeBlocks
    (segmentIndex : Nat) (segment : Segment) : List (List Recipe) :=
  let block := segment.terminalSourceKeyRecipeBlock segmentIndex
  [block, block]

def RouteShape.terminalSourceKeyRecipeBlocks
    (shape : RouteShape) : List (List Recipe) :=
  (shape.segments .first).zipIdx.flatMap fun tagged =>
    tagged.1.terminalSourceKeyRecipeBlocks tagged.2

/-- Complete doubled recipe family aligned with the terminal carrier-segment
activation word. -/
def terminalSourceKeyRecipeBlocks : List (List Recipe) :=
  allRouteShapes.flatMap RouteShape.terminalSourceKeyRecipeBlocks

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
