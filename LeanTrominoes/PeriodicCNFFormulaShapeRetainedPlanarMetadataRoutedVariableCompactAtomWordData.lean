/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariablePairAffineData
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyTagData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteShapeSelection
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorTargetAtomWordData

/-! # Compact routed-variable atom-word recipes -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairCarrierKeyWordRecipes
open RouteDescriptorPairFieldTags
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- The target-port ranks of one complete routed-variable site. -/
def routedVariableCompactTargetRanks : List Nat :=
  [0, 1, 2]

/-- Select one route in a target-major routed-variable fiber.  A rank-two
cycle descriptor is the outer anchor; the inner descriptor supplies one of
the three route terminals at the same target vertex. -/
def RouteShape.routedVariableCompactAtomWordPredicate
    (shape : RouteShape) (targetRank : Nat) : Predicate :=
  all
    [equal (routedVariablePairTargetPortRank .first) (constant 2),
      equal (routedVariablePairTargetPortRank .second)
        (constant targetRank),
      equal (routedVariablePairTargetVertexIndex .first)
        (routedVariablePairTargetVertexIndex .second),
      shape.guard .second]

/-- One normalized target-terminal recipe.  Compact terminal keys tag the
last route segment's finish endpoint in the low three bits. -/
def RouteShape.routedVariableTargetTerminalRecipe
    (shape : RouteShape) : Recipe :=
  { side := .second
    segmentIndex :=
      8 * ((shape.segments .second).length - 1) +
        CarrierNodeSourceKeys.segmentEndTag .finish
    translate := (0, 0)
    supported := true }

/-- The source-atom recipe reuses the generic carrier-key emitter only as a
unary target-index carrier.  Its fixed suffix is removed by the alternating
compact-word cleanup pass. -/
def routedVariableSourceAtomRecipe : Recipe :=
  { side := .first
    segmentIndex := 0
    translate := (0, 0)
    supported := true }

/-- Four clause-major atom occurrences contributed by one routed-variable
equality.  Terminal and source-atom recipes alternate. -/
def RouteShape.routedVariableCompactAtomWordRecipes
    (shape : RouteShape) : List Recipe :=
  [shape.routedVariableTargetTerminalRecipe,
    routedVariableSourceAtomRecipe,
    shape.routedVariableTargetTerminalRecipe,
    routedVariableSourceAtomRecipe]

/-- The three target-rank predicates of one route shape. -/
def RouteShape.routedVariableCompactAtomWordPredicates
    (shape : RouteShape) : List Predicate :=
  routedVariableCompactTargetRanks.map
    shape.routedVariableCompactAtomWordPredicate

/-- One four-recipe block aligned with each target-rank predicate. -/
def RouteShape.routedVariableCompactAtomWordRecipeBlocks
    (shape : RouteShape) : List (List Recipe) :=
  routedVariableCompactTargetRanks.map fun _ =>
    shape.routedVariableCompactAtomWordRecipes

/-- Complete fixed affine predicate family for routed-variable atom words. -/
def routedVariableCompactAtomWordPredicates : List Predicate :=
  allRouteShapes.flatMap fun shape =>
    shape.routedVariableCompactAtomWordPredicates

/-- Complete aligned fixed recipe family. -/
def routedVariableCompactAtomWordRecipeBlocks : List (List Recipe) :=
  allRouteShapes.flatMap fun shape =>
    shape.routedVariableCompactAtomWordRecipeBlocks

/-- Guarded generic key words for one tagged descriptor pair.  The later
alternating cleanup pass interprets even positions as compact terminals and
odd positions as compact source atoms. -/
def routedVariableCompactAtomRecipeKey
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (recipe : Recipe) : CarrierKeyWords.CarrierKey :=
  (match recipe.side with
    | .first => tokenFieldValue tokens .first 4
    | .second => tokenFieldValue tokens .second 2,
    recipe.segmentIndex, recipe.translate)

def routedVariableCompactAtomRecipeWord
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (active : Bool) (recipe : Recipe) : List Bool :=
  if active && recipe.supported then
    true :: CarrierKeyWords.word
      (routedVariableCompactAtomRecipeKey tokens recipe)
  else
    PaddedSupportedCandidateWords.sentinelWord

def routedVariableCompactAtomRecipeWords
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List Bool → List (List Recipe) → List (List Bool)
  | active :: actives, block :: blocks =>
      block.map (routedVariableCompactAtomRecipeWord tokens active) ++
        routedVariableCompactAtomRecipeWords tokens actives blocks
  | _, _ => []

def routedVariableCompactAtomGuardedWords
    (tokens : List RouteDescriptorPairFieldTags.Token) : List (List Bool) :=
  routedVariableCompactAtomRecipeWords tokens
    (routedVariableCompactAtomWordPredicates.map fun predicate =>
      predicate.evalTokens tokens)
    routedVariableCompactAtomWordRecipeBlocks

/-- Compact word of a route descriptor's normalized target terminal. -/
def routeDescriptorTargetTerminalCompactAtomWord
    (descriptor : RouteDescriptor) : List Bool :=
  [false, false] ++ CarrierKeyWords.word
    (descriptor.edgeIndex,
      8 * ((gridPolylineSegments descriptor.route).length - 1) +
        CarrierNodeSourceKeys.segmentEndTag .finish,
      (0, 0))

/-- Exact four-word block selected by one routed-variable route. -/
def routedVariableCompactAtomWordBlock
    (anchor route : RouteDescriptor) : List (List Bool) :=
  [routeDescriptorTargetTerminalCompactAtomWord route,
    RouteDescriptorTargetAtomWords.word anchor,
    routeDescriptorTargetTerminalCompactAtomWord route,
    RouteDescriptorTargetAtomWords.word anchor]

/-- Semantic output of one descriptor pair, independent of the finite route-
shape partition used by the compiler. -/
def routedVariableCompactAtomWordPairBlock
    (pair : RouteDescriptor × RouteDescriptor) : List (List Bool) :=
  if pair.1.targetPortRank = 2 ∧
      pair.2.targetPortRank ∈ routedVariableCompactTargetRanks ∧
      pair.1.targetVertexIndex = pair.2.targetVertexIndex then
    routedVariableCompactAtomWordBlock pair.1 pair.2
  else
    []

/-- Row-major target-major scan of all compact routed-variable words. -/
def routedVariableCompactAtomWordPairScan
    (descriptors : List RouteDescriptor) : List (List Bool) :=
  (descriptors ×ˢ descriptors).flatMap
    routedVariableCompactAtomWordPairBlock

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
