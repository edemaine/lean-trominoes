/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalSourceKeyRecipeData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairSourceKeyRecipePairData

/-! # Explicit terminal source-key recipe pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairSourceKeyRecipePairs

def terminalSourceKeyRecipePair
    (segmentIndex : Nat) (translate : Cell) (endpoint : SegmentEnd) :
    RecipePair :=
  let recipe := terminalSourceKeyRecipe segmentIndex translate endpoint
  (recipe, recipe)

def Segment.terminalSourceKeyRecipePairBlock
    (segmentIndex : Nat) (_segment : Segment) : List RecipePair :=
  neighborTranslations.flatMap fun translate =>
    [terminalSourceKeyRecipePair segmentIndex translate .start,
      terminalSourceKeyRecipePair segmentIndex translate .finish]

def Segment.terminalSourceKeyRecipePairBlocks
    (segmentIndex : Nat) (segment : Segment) : List (List RecipePair) :=
  let block := segment.terminalSourceKeyRecipePairBlock segmentIndex
  [block, block]

def RouteShape.terminalSourceKeyRecipePairBlocks
    (shape : RouteShape) : List (List RecipePair) :=
  (shape.segments .first).zipIdx.flatMap fun tagged =>
    tagged.1.terminalSourceKeyRecipePairBlocks tagged.2

def terminalSourceKeyRecipePairBlocks : List (List RecipePair) :=
  allRouteShapes.flatMap RouteShape.terminalSourceKeyRecipePairBlocks

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
