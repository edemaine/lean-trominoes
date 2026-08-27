/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendScanData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierBendRouteTailRecordData

/-! # Affine retained-bend Figure 9 tail-record selection data -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PlanarThreeSAT RouteDescriptorPairFieldTags
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

abbrev BendRouteTailRecordToken :=
  PeriodicCNFStripReduction.HorizontalRoutedRouteTailRecord.Token

/-- The sixteen canonical Figure 9 record blocks aligned with the existing
ordered bend-port predicates.  Normalized bend links stay in one slice. -/
def bendTemplateRouteTailRecordBlocks :
    List (List BendRouteTailRecordToken) :=
  allCornerPortPairs.map fun ports =>
    bendRouteTailRecordBlock ports.1 ports.2 false

def RouteShape.bendRouteTailRecordBlocks
    (shape : RouteShape) : List (List BendRouteTailRecordToken) :=
  shape.baseBendTemplates.flatMap fun _ =>
    bendTemplateRouteTailRecordBlocks

def affineBaseBendRouteTailRecordBlock
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List BendRouteTailRecordToken :=
  predicateListBlocks bendDescriptorPredicates
    (allRouteShapes.flatMap RouteShape.bendRouteTailRecordBlocks) tokens

/-- Pair-major selection of untranslated bend record blocks. -/
def affineBaseBendRouteTailRecordStream
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List BendRouteTailRecordToken :=
  TM2EndDelimitedBlockMap.mappedOutput isPairEnd
    affineBaseBendRouteTailRecordBlock tokens

def repeatNeighborBendRouteTailRecordBlock
    (block : List BendRouteTailRecordToken) :
    List BendRouteTailRecordToken :=
  neighborTranslations.flatMap fun _ => block

def affineBendRouteTailRecordBlock
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List BendRouteTailRecordToken :=
  repeatNeighborBendRouteTailRecordBlock
    (affineBaseBendRouteTailRecordBlock tokens)

def affineBendRouteTailRecordStream
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List BendRouteTailRecordToken :=
  TM2EndDelimitedBlockMap.mappedOutput isPairEnd
    affineBendRouteTailRecordBlock tokens

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
