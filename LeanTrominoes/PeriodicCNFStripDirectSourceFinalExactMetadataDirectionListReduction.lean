/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalExactMetadataPolarityOperationLookup
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderExactOperationSemantics

/-! # Reducing direct exact-block equality to source-word equality -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicOneInThreePolarityNormalizationRouteSubdivision
open PeriodicOrthocrossing
open Gadget

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalDirectionListReductionStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalDirectionListReductionVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The final-gauged source-route direction word selected by one global
source clause/literal coordinate. -/
noncomputable def directSourceFinalGaugedDirectionWord
    (symbols : List encoding.Γ) (sourceIndex : Nat × Nat) :
    List AxisDirection :=
  unitSubdivisionDirections
    (directSourceFinalGaugedIncidenceRoutes decider symbols
      sourceIndex.1 sourceIndex.2)

/-- Once every direct pair's finite prefix and dynamic tail recover its
attached final-gauged source word, the direct routed blocks and exact
metadata blocks have identical complete direction-word lists. -/
theorem directFigureNinePolarityRoutePairs_map_directions_eq_exactMetadata_of_sourceWords
    (symbols : List encoding.Γ)
    (sourceWords : ∀ index,
      index < (directFigureNinePolarityRoutePairs decider symbols).length →
      (HorizontalRoutedRouteHeader.sourceBlock
        ((directFigureNinePolarityRoutePairs
          decider symbols).getD index default).1
        ((directFigureNinePolarityRoutePairs
          decider symbols).getD index default).2).directions =
        directSourceFinalGaugedDirectionWord decider symbols
          ((directFigureNinePolarityRoutePairSourceClauseIndices
            decider symbols).getD index 0,
           ((directFigureNinePolarityRoutePairs
            decider symbols).getD index default).1.polarity.indexed.sourceLiteralIndex)) :
    (directFigureNinePolarityRoutePairs decider symbols).map
        (fun pair =>
          (HorizontalRoutedRouteHeader.block pair.1 pair.2).directions
            RetainedFigureNineRouteDirectionBlock.directions) =
      (directSourceFinalExactMetadataRouteBlocks decider symbols).map
        (fun block =>
          block.directions
            (directSourceFinalGaugedDirectionWord decider symbols)) := by
  apply List.ext_getElem
  · simp
  · intro index leftLt rightLt
    have pairLt : index <
        (directFigureNinePolarityRoutePairs decider symbols).length := by
      simpa using leftLt
    have sourceIndexLt : index <
        (directFigureNinePolarityRoutePairSourceClauseIndices
          decider symbols).length := by
      simpa using pairLt
    have exactBlockLt : index <
        (directSourceFinalExactMetadataRouteBlocks
          decider symbols).length := by
      simpa using pairLt
    simp only [List.getElem_map]
    have descriptorEq :=
      directFigureNinePolarityRoutePair_getD_sourceIndexedDescriptor_eq_exactMetadata
        decider symbols index pairLt
    have sourceWordEq := sourceWords index pairLt
    have operationEq :=
      HorizontalRoutedRouteHeader.block_directions_eq_exact_of_sourceIndexedDescriptor_eq
        (directSourceFinalGaugedDirectionWord decider symbols)
        ((directFigureNinePolarityRoutePairSourceClauseIndices
          decider symbols).getD index 0)
        ((directFigureNinePolarityRoutePairs
          decider symbols).getD index default).1
        ((directFigureNinePolarityRoutePairs
          decider symbols).getD index default).2
        ((directSourceFinalExactMetadataRouteBlocks
          decider symbols).getD index (.compatible (0, 0)))
        descriptorEq sourceWordEq
    simpa only [List.getD_eq_getElem _ _ sourceIndexLt,
      List.getD_eq_getElem _ _ pairLt,
      List.getD_eq_getElem _ _ exactBlockLt] using operationEq

end LeanTrominoes.PeriodicCNFStripReduction

end
