/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalColoredOccurrenceRoutePairSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceParentPermutation
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutePairOccurrenceDataSemantics

/-! # Grouped occurrence route-pair alignment -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Reading the retained route pair at every stable grouped index recovers
the occurrence data selected by that same index. -/
theorem directSourceFinalGroupedOccurrenceData_eq_map_routePair
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedOccurrenceData decider symbols =
      (directSourceFinalGroupedOccurrenceIndices decider symbols).map
        fun index =>
          HorizontalRoutedRouteHeader.occurrenceData
            ((directFigureNinePolarityRoutePairs
              decider symbols).getD index default).1 := by
  rw [directSourceFinalGroupedOccurrenceData_eq_map_getD]
  apply List.map_congr_left
  intro index indexMember
  have indexLt : index <
      (directSourceFinalCompiledOccurrenceData decider symbols).length :=
    directSourceFinalGroupedOccurrenceIndex_lt
      decider symbols index indexMember
  have dataEq := directSourceFinalCompiledOccurrenceData_eq_routePairs
    decider symbols
  have pairLength :
      (directSourceFinalCompiledOccurrenceData decider symbols).length =
        (directFigureNinePolarityRoutePairs decider symbols).length := by
    simpa using congrArg List.length dataEq
  have pairLt : index <
      (directFigureNinePolarityRoutePairs decider symbols).length := by
    rw [← pairLength]
    exact indexLt
  have mappedLt : index <
      ((directFigureNinePolarityRoutePairs decider symbols).map fun pair =>
        HorizontalRoutedRouteHeader.occurrenceData pair.1).length := by
    simpa using pairLt
  rw [dataEq,
    List.getD_eq_getElem _ _ mappedLt,
    List.getElem_map,
    List.getD_eq_getElem _ _ pairLt]

end LeanTrominoes.PeriodicCNFStripReduction

end
