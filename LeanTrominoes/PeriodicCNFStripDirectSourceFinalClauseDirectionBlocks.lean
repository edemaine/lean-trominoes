/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.ListFlattenWithBlockLengths
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFrameBlockLengths
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalEndpointDirections
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderClauseBlockSemantics

/-! # Clause fans recovered from the actual routed direction blocks -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PeriodicOrthocrossing
open PeriodicPlanarOneInThreeToThreeDM
open PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- Incoming directions of the stored clause-to-variable routes, retaining
the actual clause boundaries and literal order. -/
def clauseIncomingDirectionBlocks {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) : List (List AxisDirection) :=
  source.clauses.zipIdx.map fun clause =>
    clause.1.literals.zipIdx.map fun literal =>
      ((unitSubdivisionDirections (routes clause.2 literal.2)).headD .invalid).opposite

theorem clauseIncomingDirectionBlocks_flatten {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    (clauseIncomingDirectionBlocks source routes).flatten =
      (presentedIncidenceDirectionWords source routes).map
        (fun word => (word.headD .invalid).opposite) := by
  unfold clauseIncomingDirectionBlocks presentedIncidenceDirectionWords
  rw [List.flatten_eq_flatMap, List.flatMap_map, List.map_flatMap]
  simp only [List.map_map, Function.comp_def, id_eq]

theorem clauseIncomingDirectionBlocks_lengths {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    (clauseIncomingDirectionBlocks source routes).map List.length =
      source.erase.clauses.map List.length := by
  simpa only [clauseIncomingDirectionBlocks, List.map_map, List.length_map,
    List.length_zipIdx, PositionedPeriodicCNF.erase, Function.comp_def] using
    congrArg (List.map fun clause : PositionedPeriodicClause Variable => clause.literals.length)
      (List.zipIdx_map_fst 0 source.clauses)

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance clauseDirectionBlocksStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance clauseDirectionBlocksVariableDecidableEq : DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The incoming direction column of each compiled clause frame block. -/
def directSourceFinalClauseIncomingDirectionBlocks (symbols : List encoding.Γ) :
    List (List AxisDirection) :=
  (directSourceFinalClauseFrameBlocks decider symbols).map
    (List.map fun frame => (HorizontalRoutedRouteHeader.outputFirstDirection frame.header).opposite)

private theorem directSourceFinalClauseIncomingDirectionBlocks_flatten
    (symbols : List encoding.Γ) :
    (directSourceFinalClauseIncomingDirectionBlocks decider symbols).flatten =
      (presentedIncidenceDirectionWords
        (horizontalRoutedFormulaComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))
        (horizontalRoutedRoutesComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))).map
          (fun word => (word.headD .invalid).opposite) := by
  unfold directSourceFinalClauseIncomingDirectionBlocks
  rw [← List.map_flatten, directSourceFinalClauseFrameBlocks_flatten]
  have headers := directSourceFinalClauseFrames_map_header_eq_routePairs decider symbols
  have directions := congrArg
    (List.map fun header => (HorizontalRoutedRouteHeader.outputFirstDirection header).opposite)
    headers
  calc
    _ = (directFigureNinePolarityRoutePairs decider symbols).map
          (fun pair => (HorizontalRoutedRouteHeader.outputFirstDirection pair.1).opposite) := by
      simpa only [List.map_map, Function.comp_def] using directions
    _ = (directFigureNinePolarityRoutePairs decider symbols).map
          (fun pair => (((HorizontalRoutedRouteHeader.block pair.1 pair.2).directions
            RetainedFigureNineRouteDirectionBlock.directions).headD .invalid).opposite) := by
      apply List.map_congr_left
      intro pair _
      exact congrArg AxisDirection.opposite
        (HorizontalRoutedRouteHeader.outputFirstDirection_eq_completed pair.1 pair.2)
    _ = _ := by
      rw [← directFigureNinePolarityRoutePairs_map_directions_eq_horizontal,
        List.map_map]
      rfl

/-- The actual clause arities recover the boundaries of the already equal
flattened direction columns. Hence every clause gets exactly its own routes. -/
theorem directSourceFinalClauseIncomingDirectionBlocks_eq_horizontal
    (symbols : List encoding.Γ) :
    directSourceFinalClauseIncomingDirectionBlocks decider symbols =
      clauseIncomingDirectionBlocks
        (horizontalRoutedFormulaComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))
        (horizontalRoutedRoutesComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)) := by
  apply List.eq_of_flatten_eq_of_map_length_eq
  · rw [directSourceFinalClauseIncomingDirectionBlocks_flatten,
      clauseIncomingDirectionBlocks_flatten]
  · rw [clauseIncomingDirectionBlocks_lengths]
    simpa only [directSourceFinalClauseIncomingDirectionBlocks, List.map_map,
      List.length_map, Function.comp_def] using
      directSourceFinalClauseFrameBlocks_lengths_eq_horizontalRouted decider symbols

/-- The complete direct clause-fan list is assembled from the incoming
directions of the actual horizontal clauses, with their exact boundaries. -/
theorem directSourceFinalClauseFans_eq_horizontalDirectionBlocks
    (symbols : List encoding.Γ) :
    directSourceFinalClauseFans decider symbols =
      (clauseIncomingDirectionBlocks
        (horizontalRoutedFormulaComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))
        (horizontalRoutedRoutesComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))).map
          HorizontalRoutedRouteHeaderClauseFrame.fanOfDirections := by
  rw [← directSourceFinalClauseIncomingDirectionBlocks_eq_horizontal]
  change (directSourceFinalClauseFrameBlocks decider symbols).map
      HorizontalRoutedRouteHeaderClauseFrame.blockFan = _
  unfold directSourceFinalClauseIncomingDirectionBlocks
  rw [List.map_map]
  apply List.map_congr_left
  intro block blockMember
  apply HorizontalRoutedRouteHeaderClauseFrame.outputBlock_fan
    (directSourceFinalClauseDescriptors decider symbols) block blockMember
  have positive := (finalClauseFrameBlocks_spec
    (directSourceFinalClauseDescriptors decider symbols) block blockMember).1
  exact List.ne_nil_of_length_pos positive

/-- The grouped terminal labels are the literal-index groups of the actual
horizontal clauses, not just a list with the correct total length. -/
theorem directSourceFinalClauseFrameBlocks_groups_eq_horizontal
    (symbols : List encoding.Γ) :
    (directSourceFinalClauseFrameBlocks decider symbols).map
        (List.map HorizontalRoutedRouteHeaderClauseFrame.Data.group) =
      (horizontalRoutedFormulaComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.clauses.map
          (fun clause => (List.range clause.length).map terminalGroupOfLiteralIndex) := by
  have groups :
      (directSourceFinalClauseFrameBlocks decider symbols).map
          (List.map HorizontalRoutedRouteHeaderClauseFrame.Data.group) =
        (directSourceFinalClauseFrameBlocks decider symbols).map
          (fun block => (List.range block.length).map terminalGroupOfLiteralIndex) := by
    apply List.map_congr_left
    intro block member
    exact HorizontalRoutedRouteHeaderClauseFrame.outputBlock_groups
      (directSourceFinalClauseDescriptors decider symbols) block member
  rw [groups]
  simpa only [List.map_map, Function.comp_def] using
    congrArg (List.map fun length => (List.range length).map terminalGroupOfLiteralIndex)
      (directSourceFinalClauseFrameBlocks_lengths_eq_horizontalRouted decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
