/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendScanData
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyTagData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeData

/-! # Affine recipes for compact retained-bend atom words -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairCarrierKeyWordRecipes

/-- Carrier-key recipe for one normalized terminal of an untranslated bend.
The segment index includes the low endpoint tag used by compact retained-atom
words. -/
def BendTemplate.compactTerminalRecipe
    (template : BendTemplate) (outgoing : Bool) : Recipe :=
  { side := .first
    segmentIndex := if outgoing then
        8 * (template.incomingSegmentIndex + 1) +
          CarrierNodeSourceKeys.segmentEndTag .start
      else
        8 * template.incomingSegmentIndex +
          CarrierNodeSourceKeys.segmentEndTag .finish
    translate := template.translate
    supported := true }

/-- Four clause-major endpoint occurrences contributed by one bend equality. -/
def BendTemplate.compactAtomWordRecipes
    (template : BendTemplate) : List Recipe :=
  [template.compactTerminalRecipe false,
    template.compactTerminalRecipe true,
    template.compactTerminalRecipe false,
    template.compactTerminalRecipe true]

/-- The same endpoint recipe block is aligned with every possible compass-port
classification of one fixed bend position. -/
def BendTemplate.compactAtomWordRecipeBlocks
    (template : BendTemplate) (shape : RouteShape) : List (List Recipe) :=
  (template.descriptorPredicates shape).map fun _ =>
    template.compactAtomWordRecipes

/-- Endpoint recipe blocks aligned with every bend predicate of one route
shape. -/
def RouteShape.bendCompactAtomWordRecipeBlocks
    (shape : RouteShape) : List (List Recipe) :=
  shape.baseBendTemplates.flatMap fun template =>
    template.compactAtomWordRecipeBlocks shape

/-- Complete fixed endpoint-recipe family aligned with
`bendDescriptorPredicates`. -/
def bendCompactAtomWordRecipeBlocks : List (List Recipe) :=
  allRouteShapes.flatMap RouteShape.bendCompactAtomWordRecipeBlocks

/-- Activity-guarded carrier-key words for every affine bend candidate of one
tagged descriptor pair. Active words still carry the emitter's leading
support bit; a later finite transducer replaces it with the compact terminal
constructor tag and removes rejection sentinels. -/
def bendCompactAtomGuardedWords
    (tokens : List RouteDescriptorPairFieldTags.Token) : List (List Bool) :=
  words tokens
    (bendDescriptorPredicates.map fun predicate => predicate.evalTokens tokens)
    bendCompactAtomWordRecipeBlocks

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
