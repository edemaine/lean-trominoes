/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendScanData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendRouteDirectionWords
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequestBatchInnerCompiler

/-! # Affine selection data for complete retained-bend route words -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PlanarThreeSAT RouteDescriptorPairFieldTags
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

abbrev BendRouteDirectionToken :=
  PeriodicThreeDM.NormalizationDirectionRequest.Batch.NormalizedToken

/-- Add one explicit boundary after a complete bend-route direction word. -/
def delimitedBendRouteDirections
    (directions : List AxisDirection) : List BendRouteDirectionToken :=
  directions.map .direction ++ [.routeEnd]

/-- Four route-delimited direction words for one fixed corner equality
drawing, in clause-major incidence order. -/
def canonicalBendRouteDirectionBlock
    (firstPort secondPort : CornerPort) : List BendRouteDirectionToken :=
  delimitedBendRouteDirections
      (bendRouteDirections firstPort secondPort 0 0) ++
    delimitedBendRouteDirections
      (bendRouteDirections firstPort secondPort 0 1) ++
    delimitedBendRouteDirections
      (bendRouteDirections firstPort secondPort 1 0) ++
    delimitedBendRouteDirections
      (bendRouteDirections firstPort secondPort 1 1)

/-- The sixteen finite direction blocks aligned with the existing ordered
bend-port predicates. -/
def bendTemplateRouteDirectionBlocks :
    List (List BendRouteDirectionToken) :=
  allCornerPortPairs.map fun ports =>
    canonicalBendRouteDirectionBlock ports.1 ports.2

/-- Direction-word output blocks aligned with every bend predicate of one
fixed route shape. -/
def RouteShape.bendRouteDirectionBlocks
    (shape : RouteShape) : List (List BendRouteDirectionToken) :=
  shape.baseBendTemplates.flatMap fun _ =>
    bendTemplateRouteDirectionBlocks

/-- Selected complete bend-route words for one untranslated descriptor-pair
record. -/
def affineBaseBendRouteDirectionBlock
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List BendRouteDirectionToken :=
  predicateListBlocks bendDescriptorPredicates
    (allRouteShapes.flatMap RouteShape.bendRouteDirectionBlocks) tokens

/-- Pair-major affine scan selecting all untranslated bend-route direction
words, with one explicit boundary after every route. -/
def affineBaseBendRouteDirectionStream
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List BendRouteDirectionToken :=
  TM2EndDelimitedBlockMap.mappedOutput isPairEnd
    affineBaseBendRouteDirectionBlock tokens

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
