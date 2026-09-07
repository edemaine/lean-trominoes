/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceDirectionWords
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalExactMetadataDirectionListReduction
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceWitness

/-! # Direct Figure 9 source words agree with exact final metadata -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicOrthocrossing
open Gadget

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance sourceWordsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance sourceWordsVariableDecidableEq : DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Every direct header/tail pair denotes the final gauged source direction
word at its attached absolute clause and literal indices. -/
theorem directFigureNinePolarityRoutePair_sourceWord
    (symbols : List encoding.Γ) (index : Nat)
    (indexLt : index < (directFigureNinePolarityRoutePairs decider symbols).length) :
    (HorizontalRoutedRouteHeader.sourceBlock
      ((directFigureNinePolarityRoutePairs decider symbols).getD index default).1
      ((directFigureNinePolarityRoutePairs decider symbols).getD index default).2).directions =
      directSourceFinalGaugedDirectionWord decider symbols
        ((directFigureNinePolarityRoutePairSourceClauseIndices decider symbols).getD index 0,
          ((directFigureNinePolarityRoutePairs decider symbols).getD index default).1.polarity.indexed.sourceLiteralIndex) := by
  obtain ⟨occurrence, pairEq, generatedEq, ⟨witness⟩⟩ :=
    exists_directSourceFinalOccurrence decider symbols index indexLt
  rw [← pairEq, ← generatedEq]
  have sourceLocal : (directSourceFormula decider symbols).IsLocal :=
    sourceFormula_isLocal (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)
  have sourceWidth : (directSourceFormula decider symbols).WidthAtMost 3 :=
    sourceFormula_widthAtMostThree (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)
  have sourceOccurrences :
      @PeriodicCNF.OccurrencesAtMost Variable instBEqOfDecidableEq
        (by infer_instance) 3 (directSourceFormula decider symbols) := by
    exact PeriodicCNF.occurrencesAtMost_congr_beq
      _ _ (by infer_instance) (by infer_instance) 3 _
      (sourceFormula_occurrencesAtMostThree (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))
  have sourceNonempty : ∀ clause ∈ (directSourceFormula decider symbols).clauses, clause ≠ [] :=
    sourceFormula_clausesNonempty (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)
  exact witness.sourceDirectionWord sourceLocal sourceWidth sourceOccurrences sourceNonempty

/-- The executable direct blocks and exact metadata blocks have identical
complete direction-word lists, including all polarity operations. -/
theorem directFigureNinePolarityRoutePairs_map_directions_eq_exactMetadata
    (symbols : List encoding.Γ) :
    (directFigureNinePolarityRoutePairs decider symbols).map
        (fun pair => (HorizontalRoutedRouteHeader.block pair.1 pair.2).directions
          RetainedFigureNineRouteDirectionBlock.directions) =
      (directSourceFinalExactMetadataRouteBlocks decider symbols).map
        (fun block => block.directions (directSourceFinalGaugedDirectionWord decider symbols)) :=
  directFigureNinePolarityRoutePairs_map_directions_eq_exactMetadata_of_sourceWords
    decider symbols (directFigureNinePolarityRoutePair_sourceWord decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
