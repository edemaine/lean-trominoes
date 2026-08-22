/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendNextSliceSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineBendPortPredicateData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBlockStreamData

/-! # Finite affine retained-bend descriptor scan -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PlanarThreeSAT RouteDescriptorPairFieldTags
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- The four bend ports in a fixed exhaustive order. -/
def allCornerPorts : List CornerPort :=
  [.west, .east, .south, .north]

/-- The sixteen ordered bend-port pairs. -/
def allCornerPortPairs : List (CornerPort × CornerPort) :=
  allCornerPorts ×ˢ allCornerPorts

/-- The stored edge index is the one-field diagonal key of a descriptor pair. -/
def sameEdgeIndexPredicate : Predicate :=
  equal (field .first 2) (field .second 2)

/-- Bend templates for one untranslated occurrence of one selected route. -/
def RouteShape.baseBendTemplates
    (shape : RouteShape) : List BendTemplate :=
  bendTemplatesAux (0, 0) 0 (shape.points .first)

/-- Select one shape, one bend position, and one ordered port pair on the
edge-index diagonal of the descriptor square. -/
def BendTemplate.descriptorPredicate
    (shape : RouteShape) (template : BendTemplate)
    (ports : CornerPort × CornerPort) : Predicate :=
  all
    [sameEdgeIndexPredicate,
      shape.guard .first,
      template.portPredicate ports.1 ports.2]

/-- Predicates classifying every bend of one selected route shape. -/
def RouteShape.bendDescriptorPredicates
    (shape : RouteShape) : List Predicate :=
  shape.baseBendTemplates.flatMap fun template =>
    allCornerPortPairs.map fun ports =>
      template.descriptorPredicate shape ports

/-- Corresponding fixed two-token canonical bend descriptor blocks. -/
def RouteShape.bendDescriptorBlocks
    (shape : RouteShape) :
    List (List PeriodicCNF.FormulaShapeDirectionOrdering.Token) :=
  shape.baseBendTemplates.flatMap fun _ =>
    allCornerPortPairs.map fun ports =>
      canonicalBendDescriptorBlock ports.1 ports.2 false

/-- Complete fixed predicate list for one untranslated route occurrence. -/
def bendDescriptorPredicates : List Predicate :=
  allRouteShapes.flatMap RouteShape.bendDescriptorPredicates

/-- Complete fixed output-block list aligned with `bendDescriptorPredicates`. -/
def bendDescriptorBlocks :
    List (List PeriodicCNF.FormulaShapeDirectionOrdering.Token) :=
  allRouteShapes.flatMap RouteShape.bendDescriptorBlocks

/-- Selected retained-bend descriptors for one untranslated descriptor route. -/
def affineBaseBendDescriptorBlock
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List PeriodicCNF.FormulaShapeDirectionOrdering.Token :=
  predicateListBlocks bendDescriptorPredicates bendDescriptorBlocks tokens

/-- Repeat one route-local bend block in the canonical neighboring-translation
order.  Bend descriptors are translation independent because their canonical
relative-slice bit is always false. -/
def repeatNeighborBendDescriptorBlock
    (block : List PeriodicCNF.FormulaShapeDirectionOrdering.Token) :
    List PeriodicCNF.FormulaShapeDirectionOrdering.Token :=
  neighborTranslations.flatMap fun _ => block

/-- Complete bend descriptor block selected from one tagged descriptor pair. -/
def affineBendDescriptorBlock
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List PeriodicCNF.FormulaShapeDirectionOrdering.Token :=
  repeatNeighborBendDescriptorBlock
    (affineBaseBendDescriptorBlock tokens)

/-- Pair-major finite affine retained-bend scan.  Equality of the stored edge
indices restricts a self-indexed descriptor square to its diagonal. -/
def affineBendDescriptorStream
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List PeriodicCNF.FormulaShapeDirectionOrdering.Token :=
  TM2EndDelimitedBlockMap.mappedOutput isPairEnd
    affineBendDescriptorBlock tokens

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
