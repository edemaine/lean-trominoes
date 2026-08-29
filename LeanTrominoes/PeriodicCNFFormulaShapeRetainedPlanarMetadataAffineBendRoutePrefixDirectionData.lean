/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendRouteDirectionData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataFallbackPrefixDirectionWords

/-! # Affine selection data for retained-bend route source prefixes -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PlanarThreeSAT RouteDescriptorPairFieldTags
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- Four route-delimited source-prefix words for one fixed corner equality
drawing, in clause-major incidence order. -/
def canonicalBendRoutePrefixDirectionBlock
    (firstPort secondPort : CornerPort) : List BendRouteDirectionToken :=
  delimitedBendRouteDirections
      (bendRoutePrefixDirections firstPort secondPort 0 0) ++
    delimitedBendRouteDirections
      (bendRoutePrefixDirections firstPort secondPort 0 1) ++
    delimitedBendRouteDirections
      (bendRoutePrefixDirections firstPort secondPort 1 0) ++
    delimitedBendRouteDirections
      (bendRoutePrefixDirections firstPort secondPort 1 1)

/-- The sixteen finite source-prefix blocks aligned with the existing
ordered bend-port predicates. -/
def bendTemplateRoutePrefixDirectionBlocks :
    List (List BendRouteDirectionToken) :=
  allCornerPortPairs.map fun ports =>
    canonicalBendRoutePrefixDirectionBlock ports.1 ports.2

/-- Source-prefix blocks aligned with every bend predicate of one fixed
route shape. -/
def RouteShape.bendRoutePrefixDirectionBlocks
    (shape : RouteShape) : List (List BendRouteDirectionToken) :=
  shape.baseBendTemplates.flatMap fun _ =>
    bendTemplateRoutePrefixDirectionBlocks

/-- Selected bend-route source prefixes for one untranslated descriptor-pair
record. -/
def affineBaseBendRoutePrefixDirectionBlock
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List BendRouteDirectionToken :=
  predicateListBlocks bendDescriptorPredicates
    (allRouteShapes.flatMap RouteShape.bendRoutePrefixDirectionBlocks) tokens

/-- Pair-major affine scan selecting all untranslated bend-route source
prefixes, with one explicit boundary after every route. -/
def affineBaseBendRoutePrefixDirectionStream
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List BendRouteDirectionToken :=
  TM2EndDelimitedBlockMap.mappedOutput isPairEnd
    affineBaseBendRoutePrefixDirectionBlock tokens

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
