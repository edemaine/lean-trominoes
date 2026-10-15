/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalIncidenceIndexFields
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Presented.PeriodicCNFStripDirectSourceFinalPresentedDirectionWords
import LeanTrominoes.ThreeDM.Reduction.FromSAT.PeriodicPlanarOneInThreeToThreeDMOccurrenceEntryIndices

/-! # The direct stored word belongs to the same tagged source occurrence -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Selecting the direct header/tail pair at an actual entry's presentation
index recovers that same entry's complete stored geometric route word. -/
theorem directFigureNinePolarityRoutePair_directions_of_occurrenceAt
    (symbols : List encoding.Γ) (atom : RoutedVariable) (slot : OccurrenceSlot)
    (tagged : TaggedOccurrence RoutedVariable)
    (lookup : occurrenceAt (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.ProgramSource.formulaOfSymbols decider symbols)).erase atom slot = some tagged) :
    let pair := (directFigureNinePolarityRoutePairs decider symbols).getD
      (occurrenceEntryIndex (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.ProgramSource.formulaOfSymbols decider symbols)).erase (atom, slot)) default
    (HorizontalRoutedRouteHeader.block pair.1 pair.2).directions
        PeriodicOrthocrossing.RetainedFigureNineRouteDirectionBlock.directions =
      unitSubdivisionDirections (horizontalRoutedRoutesComputed
        (PeriodicCNF.ProgramSource.formulaOfSymbols decider symbols) tagged.2.1 tagged.2.2) := by
  let source := PeriodicCNF.ProgramSource.formulaOfSymbols decider symbols
  let positioned := horizontalSemanticNormalizedRibbonSource source
  let word := fun pair : HorizontalRoutedRouteHeaderTail.Header × List AxisDirection =>
    (HorizontalRoutedRouteHeader.block pair.1 pair.2).directions
      PeriodicOrthocrossing.RetainedFigureNineRouteDirectionBlock.directions
  let field := fun tagged : TaggedOccurrence RoutedVariable =>
    unitSubdivisionDirections (horizontalRoutedRoutesComputed source tagged.2.1 tagged.2.2)
  have selected := PeriodicOneInThreeToThreeDM.taggedLiterals_map_getD_of_occurrenceAt
    positioned.erase atom slot tagged lookup field (word default)
  change (presentedIncidenceIndexFields positioned
      (fun clauseIndex literalIndex => unitSubdivisionDirections
        (horizontalRoutedRoutesComputed source clauseIndex literalIndex))).getD
      (occurrenceEntryIndex positioned.erase (atom, slot)) (word default) = field tagged at selected
  rw [presentedIncidenceIndexFields_horizontal_normalized,
    ← presentedIncidenceDirectionWords_eq_indexFields,
    ← directFigureNinePolarityRoutePairs_map_directions_eq_horizontal decider symbols] at selected
  rw [List.getD_map (directFigureNinePolarityRoutePairs decider symbols) default word] at selected
  exact selected

end LeanTrominoes.PeriodicCNFStripReduction

end
