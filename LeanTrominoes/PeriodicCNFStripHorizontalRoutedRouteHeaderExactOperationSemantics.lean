/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderData
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationMetadataRouteOperationSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixLocalDirectionSemantics

/-! # Exact operation semantics of completed routed headers -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteHeader

open PeriodicCNF.ClauseProfilePolarityRouteOperation
open PeriodicCNF.FormulaShapeFigureNineRoutePrefix
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open PeriodicOneInThreePolarityNormalizationRouteSubdivision
open PeriodicOrthocrossing

/-- The underlying retained Figure 9 block selected by a header, before its
polarity operation is applied. -/
def sourceBlock (header : Header)
    (sourceTailDirections : List AxisDirection) :
    RetainedFigureNineRouteDirectionBlock :=
  match header.figurePrefix with
  | .local query => .local query
  | .inherited _ query => .inherited query sourceTailDirections

/-- Completing a header with a dynamic tail does not change the common
finite-template local query selected by its prefix descriptor. -/
@[simp] theorem sourceBlock_localQuery
    (header : Header) (sourceTailDirections : List AxisDirection) :
    (sourceBlock header sourceTailDirections).localQuery =
      header.figurePrefix.localQuery := by
  rcases header with ⟨polarity, figurePrefix⟩
  cases figurePrefix <;> rfl

/-- `block` is the header's polarity operation applied to `sourceBlock`. -/
theorem block_eq_operationBlock_sourceBlock
    (header : Header) (sourceTailDirections : List AxisDirection) :
    block header sourceTailDirections =
      operationBlock header.polarity.operation
        (sourceBlock header sourceTailDirections) := by
  rcases header with ⟨polarity, figurePrefix⟩
  cases figurePrefix <;> rfl

/-- Once a direct header and an exact metadata block name the same global
source incidence and operation, equality of their underlying source words
lifts through all four polarity route operations. -/
theorem block_directions_eq_exact_of_sourceIndexedDescriptor_eq
    (sourceDirections : Nat × Nat → List AxisDirection)
    (sourceClauseIndex : Nat)
    (header : Header) (sourceTailDirections : List AxisDirection)
    (exactBlock : RouteDirectionBlock (Nat × Nat))
    (descriptorEq :
      sourceIndexedDescriptorOf sourceClauseIndex
          header.polarity.indexed =
        exactBlock.sourceIndexedDescriptor)
    (sourceDirectionsEq :
      (sourceBlock header sourceTailDirections).directions =
        sourceDirections
          (sourceClauseIndex,
            header.polarity.indexed.sourceLiteralIndex)) :
    (block header sourceTailDirections).directions
        RetainedFigureNineRouteDirectionBlock.directions =
      exactBlock.directions sourceDirections := by
  rcases header with ⟨⟨sourceSlot, operation⟩, figurePrefix⟩
  rcases exactBlock with
    exactBlock | exactBlock | exactBlock | exactBlock <;>
    rcases exactBlock with ⟨exactClauseIndex, exactLiteralIndex⟩ <;>
    cases sourceSlot <;> cases operation <;> cases figurePrefix <;>
    simp_all [sourceBlock, block, operationBlock,
      Descriptor.indexed, sourceIndexedDescriptorOf,
      RouteDirectionBlock.sourceIndexedDescriptor,
      RouteDirectionBlock.directions]

end HorizontalRoutedRouteHeader
end PeriodicCNFStripReduction
end LeanTrominoes
