/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.EndDelimitedBlockFixedCopiesBlockSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNinePolarityRouteTailPairs
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalColoredRoutedRequestBlockCompiler

/-! # Block semantics of direct colored routed requests -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalColoredRoutedRequestSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalColoredRoutedRequestSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Explicit header/tail pairs underlying the retained direct Figure 9 route
record stream. -/
def directFigureNinePolarityRoutePairs
    (symbols : List encoding.Γ) :
    List (HorizontalRoutedRouteHeaderTail.Header × List AxisDirection) :=
  PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail.sourcePairs
    (PeriodicCNF.FormulaShapeRetainedFigureNineDirection.descriptors
      (directSourceFormula decider symbols))
    (PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail.tailTables
      (directSourceFormula decider symbols))

/-- Compact routed-request payload of one explicit header/tail pair. -/
def directFigureNinePolarityRoutedRequestBody
    (pair : HorizontalRoutedRouteHeaderTail.Header × List AxisDirection) :
    List HorizontalRoutedRouteHeaderTailBlock.Token :=
  (HorizontalRoutedRouteDirectionRequest.tokens
      (HorizontalRoutedRouteHeader.block pair.1 pair.2)).map
    HorizontalRoutedRouteHeaderTailBlock.Token.request

/-- The retained recursive stream is serialization of the explicit direct
pair list. -/
theorem directFigureNinePolarityRouteTailRecords_eq_records
    (symbols : List encoding.Γ) :
    directFigureNinePolarityRouteTailRecords decider symbols =
      HorizontalRoutedRouteHeaderTail.records
        (directFigureNinePolarityRoutePairs decider symbols) := by
  unfold directFigureNinePolarityRouteTailRecords
    PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail.records
    directFigureNinePolarityRoutePairs
  exact
    PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail.sourceRecords_eq_records
      _ _

/-- Boundary-preserving completion produces exactly one complete request
block for every explicit retained header/tail pair. -/
theorem directFigureNinePolarityRoutedRequestBlockTokens_eq_blocks
    (symbols : List encoding.Γ) :
    directFigureNinePolarityRoutedRequestBlockTokens decider symbols =
      (directFigureNinePolarityRoutePairs decider symbols).flatMap
        fun pair =>
          HorizontalRoutedRouteHeaderTailBlock.requestBlock pair.1 pair.2 := by
  unfold directFigureNinePolarityRoutedRequestBlockTokens
  rw [directFigureNinePolarityRouteTailRecords_eq_records,
    HorizontalRoutedRouteHeaderTailBlock.output_records]

private theorem requestBlock_eq_completeBlock
    (pair : HorizontalRoutedRouteHeaderTail.Header × List AxisDirection) :
    HorizontalRoutedRouteHeaderTailBlock.requestBlock pair.1 pair.2 =
      EndDelimitedBlockFixedCopies.completeBlock
        HorizontalRoutedRouteHeaderTailBlock.Token.requestEnd
        (directFigureNinePolarityRoutedRequestBody pair) := by
  rfl

private theorem routedRequestBodies_continue
    (pairs : List
      (HorizontalRoutedRouteHeaderTail.Header × List AxisDirection)) :
    ∀ body ∈ pairs.map directFigureNinePolarityRoutedRequestBody,
      ∀ token ∈ body, DirectFinalColoredRoutedRequestBlock.isEnd token = false := by
  intro body bodyMember token tokenMember
  obtain ⟨pair, _, rfl⟩ := List.mem_map.mp bodyMember
  unfold directFigureNinePolarityRoutedRequestBody at tokenMember
  obtain ⟨routeToken, _, rfl⟩ := List.mem_map.mp tokenMember
  rfl

/-- Three-color copying of the retained route stream is exactly three copies
of each complete physical request block, in pair-major/color-minor order. -/
theorem directFigureNinePolarityColoredRoutedRequestBlockTokens_eq_blocks
    (symbols : List encoding.Γ) :
    directFigureNinePolarityColoredRoutedRequestBlockTokens decider symbols =
      (directFigureNinePolarityRoutePairs decider symbols).flatMap
        fun pair =>
          EndDelimitedBlockFixedCopies.copiedBlock 3
            (HorizontalRoutedRouteHeaderTailBlock.requestBlock
              pair.1 pair.2) := by
  unfold directFigureNinePolarityColoredRoutedRequestBlockTokens
    DirectFinalColoredRoutedRequestBlock.copied
  rw [directFigureNinePolarityRoutedRequestBlockTokens_eq_blocks]
  have sourceEq :
      (directFigureNinePolarityRoutePairs decider symbols).flatMap
          (fun pair =>
            HorizontalRoutedRouteHeaderTailBlock.requestBlock
              pair.1 pair.2) =
        ((directFigureNinePolarityRoutePairs decider symbols).map
          directFigureNinePolarityRoutedRequestBody).flatMap
            (EndDelimitedBlockFixedCopies.completeBlock
              HorizontalRoutedRouteHeaderTailBlock.Token.requestEnd) := by
    rw [List.flatMap_map]
    apply List.flatMap_congr
    intro pair _
    exact requestBlock_eq_completeBlock pair
  rw [sourceEq,
    EndDelimitedBlockFixedCopies.copiedTokens_completeBlocks
      3 DirectFinalColoredRoutedRequestBlock.isEnd
      HorizontalRoutedRouteHeaderTailBlock.Token.requestEnd rfl
      ((directFigureNinePolarityRoutePairs decider symbols).map
        directFigureNinePolarityRoutedRequestBody)
      (routedRequestBodies_continue
        (directFigureNinePolarityRoutePairs decider symbols)),
    List.flatMap_map]
  apply List.flatMap_congr
  intro pair _
  rw [requestBlock_eq_completeBlock]

/-- The compiled direct colored route stream has the same explicit complete
block decomposition. -/
theorem directSourceFinalColoredRoutedRequestBlockTokens_eq_blocks
    (symbols : List encoding.Γ) :
    directSourceFinalColoredRoutedRequestBlockTokens decider symbols =
      (directFigureNinePolarityRoutePairs decider symbols).flatMap
        fun pair =>
          EndDelimitedBlockFixedCopies.copiedBlock 3
            (HorizontalRoutedRouteHeaderTailBlock.requestBlock
              pair.1 pair.2) := by
  rw [directSourceFinalColoredRoutedRequestBlockTokens_eq,
    directFigureNinePolarityColoredRoutedRequestBlockTokens_eq_blocks]

end LeanTrominoes.PeriodicCNFStripReduction

end
