/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceMetadata
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutePairProfileCoordinateBlocks

/-! # One source witness for every direct Figure 9 occurrence -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open FormulaShapeFigureNinePolarityRouteTail
open FormulaShapeRetainedFigureNineSourceTail

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance sourceOccurrenceStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance sourceOccurrenceVariableDecidableEq : DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- A common proof-side stream for direct headers, tails, and both levels of
source-clause indexing. -/
def directSourceFinalOccurrences (symbols : List encoding.Γ) : List SourceOccurrence :=
  occurrences (directSourceFormula decider symbols)

@[simp] theorem directSourceFinalOccurrences_map_pair (symbols : List encoding.Γ) :
    (directSourceFinalOccurrences decider symbols).map SourceOccurrence.pair =
      directFigureNinePolarityRoutePairs decider symbols := by
  exact sourceOccurrences_map_pair _ _

theorem directSourceFinalOccurrences_map_generatedClauseIndex
    (symbols : List encoding.Γ) :
    (directSourceFinalOccurrences decider symbols).map
        SourceOccurrence.generatedClauseIndex =
      directFigureNinePolarityRoutePairSourceClauseIndices decider symbols := by
  rw [directFigureNinePolarityRoutePairSourceClauseIndices_eq_profileCoordinateBlocks]
  exact sourceOccurrences_map_generatedClauseIndex _ _

/-- Every absolute output index selects one coherent witness. In particular,
the tail's original parent is the parent named by the selected metadata. -/
theorem exists_directSourceFinalOccurrence
    (symbols : List encoding.Γ) (index : Nat)
    (indexLt : index < (directFigureNinePolarityRoutePairs decider symbols).length) :
    ∃ occurrence : SourceOccurrence,
      occurrence.pair = (directFigureNinePolarityRoutePairs decider symbols).getD
        index default ∧
      occurrence.generatedClauseIndex =
        (directFigureNinePolarityRoutePairSourceClauseIndices decider symbols).getD
          index 0 ∧
      Nonempty (OccurrenceWitness (directSourceFormula decider symbols) occurrence) := by
  have lengthEq : (directSourceFinalOccurrences decider symbols).length =
      (directFigureNinePolarityRoutePairs decider symbols).length := by
    simpa only [List.length_map] using congrArg List.length
      (directSourceFinalOccurrences_map_pair decider symbols)
  have occurrenceLt : index < (directSourceFinalOccurrences decider symbols).length := by
    rwa [lengthEq]
  let occurrence := (directSourceFinalOccurrences decider symbols)[index]
  have occurrenceMember : occurrence ∈ directSourceFinalOccurrences decider symbols :=
    List.getElem_mem occurrenceLt
  have pairEq := congrArg (fun values => values[index]?)
    (directSourceFinalOccurrences_map_pair decider symbols)
  simp only [List.getElem?_map, List.getElem?_eq_getElem occurrenceLt,
    List.getElem?_eq_getElem indexLt, Option.map_some] at pairEq
  have sourceIndexLt : index <
      (directFigureNinePolarityRoutePairSourceClauseIndices decider symbols).length := by
    simpa using indexLt
  have generatedEq := congrArg (fun values => values[index]?)
    (directSourceFinalOccurrences_map_generatedClauseIndex decider symbols)
  simp only [List.getElem?_map, List.getElem?_eq_getElem occurrenceLt,
    List.getElem?_eq_getElem sourceIndexLt, Option.map_some] at generatedEq
  refine ⟨occurrence, ?_, ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ indexLt]
    exact Option.some.inj pairEq
  · rw [List.getD_eq_getElem _ _ sourceIndexLt]
    exact Option.some.inj generatedEq
  · apply occurrenceWitness (directSourceFormula decider symbols)
    · simpa only [directSourceFormula] using sourceFormula_widthAtMostThree
        (PolySpaceCompiler.formulaOfSymbols decider symbols)
    · simpa only [directSourceFormula] using sourceFormula_clausesNonempty
        (PolySpaceCompiler.formulaOfSymbols decider symbols)
    · exact occurrenceMember

end LeanTrominoes.PeriodicCNFStripReduction

end
