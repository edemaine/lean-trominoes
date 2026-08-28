/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendScanData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataTerminalColumnData
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Affine selection data for retained-bend terminal columns -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PlanarThreeSAT RouteDescriptorPairFieldTags
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- Sixteen finite port-pair blocks aligned with the existing bend
predicates. -/
def bendTemplatePortBlocks {Output : Type}
    (block : CornerPort → CornerPort → List Output) :
    List (List Output) :=
  allCornerPortPairs.map fun ports => block ports.1 ports.2

/-- Port-pair output blocks aligned with every bend predicate of one route
shape. -/
def RouteShape.bendPortBlocks {Output : Type}
    (shape : RouteShape)
    (block : CornerPort → CornerPort → List Output) :
    List (List Output) :=
  shape.baseBendTemplates.flatMap fun _ =>
    bendTemplatePortBlocks block

/-- Select arbitrary fixed port-pair blocks for every untranslated bend of
one tagged descriptor pair. -/
def affineBaseBendPortBlock {Output : Type}
    (block : CornerPort → CornerPort → List Output)
    (tokens : List RouteDescriptorPairFieldTags.Token) : List Output :=
  predicateListBlocks bendDescriptorPredicates
    (allRouteShapes.flatMap fun shape => shape.bendPortBlocks block) tokens

/-- Pair-major affine scan for arbitrary fixed bend port-pair blocks. -/
def affineBaseBendPortStream {Output : Type}
    (block : CornerPort → CornerPort → List Output)
    (tokens : List RouteDescriptorPairFieldTags.Token) : List Output :=
  TM2EndDelimitedBlockMap.mappedOutput isPairEnd
    (affineBaseBendPortBlock block) tokens

/-- Unary direction fields of one four-incidence bend block. -/
def canonicalBendTerminalDirectionBlock
    (firstPort secondPort : CornerPort) :
    List UnaryFieldEncoderMachine.Symbol :=
  UnaryFieldEncoderMachine.unaryFields
    (terminalDataDirectionRanks
      (bendRouteTerminalDataBlock firstPort secondPort))

/-- Unary radial fields of one four-incidence bend block. -/
def canonicalBendTerminalRadialBlock
    (firstPort secondPort : CornerPort) :
    List UnaryFieldEncoderMachine.Symbol :=
  UnaryFieldEncoderMachine.unaryFields
    (terminalDataRadialLengths
      (bendRouteTerminalDataBlock firstPort secondPort))

/-- Selected unary direction fields of all untranslated bends. -/
def bendTerminalDirectionBlocks :
    List (List UnaryFieldEncoderMachine.Symbol) :=
  allRouteShapes.flatMap fun shape =>
    shape.bendPortBlocks canonicalBendTerminalDirectionBlock

/-- Selected unary radial fields aligned with the same predicate table. -/
def bendTerminalRadialBlocks :
    List (List UnaryFieldEncoderMachine.Symbol) :=
  allRouteShapes.flatMap fun shape =>
    shape.bendPortBlocks canonicalBendTerminalRadialBlock

/-- Select terminal-direction fields for one tagged descriptor pair. -/
def affineBaseBendTerminalDirectionBlock
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List UnaryFieldEncoderMachine.Symbol :=
  predicateListBlocks bendDescriptorPredicates
    bendTerminalDirectionBlocks tokens

/-- Select terminal-radial fields for one tagged descriptor pair. -/
def affineBaseBendTerminalRadialBlock
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List UnaryFieldEncoderMachine.Symbol :=
  predicateListBlocks bendDescriptorPredicates
    bendTerminalRadialBlocks tokens

/-- Selected unary direction fields of all untranslated bends. -/
def affineBaseBendTerminalDirectionStream
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List UnaryFieldEncoderMachine.Symbol :=
  TM2EndDelimitedBlockMap.mappedOutput isPairEnd
    affineBaseBendTerminalDirectionBlock tokens

/-- Selected unary radial fields of all untranslated bends. -/
def affineBaseBendTerminalRadialStream
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List UnaryFieldEncoderMachine.Symbol :=
  TM2EndDelimitedBlockMap.mappedOutput isPairEnd
    affineBaseBendTerminalRadialBlock tokens

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
