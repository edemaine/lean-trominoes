/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripHorizontalIncidenceIndexFields
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFanHorizontalSemantics
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMOccurrenceEntryIndices

/-! # Compiled clause endpoint fields belong to the actual source occurrence -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance clauseOccurrenceStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

/-- Clause fans and groups retain the actual normalized clause/literal
presentation positions used by variable occurrence lookup. -/
theorem directSourceFinalClauseFrames_fan_groups_eq_normalized
    (symbols : List encoding.Γ) :
    (directSourceFinalClauseFrames decider symbols).map
        (fun frame => (frame.clauseFan, frame.group)) =
      presentedIncidenceIndexFields (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))
        (fun clauseIndex literalIndex =>
          (horizontalOccurrenceClauseRibbonFanDataComputed
            (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols, clauseIndex),
          terminalGroupOfLiteralIndex literalIndex)) := by
  rw [presentedIncidenceIndexFields_horizontal_normalized,
    presentedIncidenceIndexFields_eq_clauseRanges]
  exact directSourceFinalClauseFrames_fan_groups_eq_horizontal decider symbols

/-- A compiled clause frame at the source entry's recovered position has
that same tagged occurrence's actual clause fan and terminal group. -/
theorem directSourceFinalClauseFrame_fields_of_occurrenceAt
    (symbols : List encoding.Γ) (atom : RoutedVariable) (slot : OccurrenceSlot)
    (tagged : TaggedOccurrence RoutedVariable)
    (lookup : occurrenceAt (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase atom slot = some tagged) :
    let frame := (directSourceFinalClauseFrames decider symbols).getD
      (occurrenceEntryIndex (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase (atom, slot)) default
    (frame.clauseFan, frame.group) =
      (horizontalOccurrenceClauseRibbonFanDataComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols, tagged.2.1),
      terminalGroupOfLiteralIndex tagged.2.2) := by
  let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols
  let positioned := horizontalSemanticNormalizedRibbonSource source
  let field := fun tagged : TaggedOccurrence RoutedVariable =>
    (horizontalOccurrenceClauseRibbonFanDataComputed (source, tagged.2.1),
      terminalGroupOfLiteralIndex tagged.2.2)
  let fallback : HorizontalRoutedRouteHeaderClauseFrame.Data := default
  have selected := PeriodicOneInThreeToThreeDM.taggedLiterals_map_getD_of_occurrenceAt
    positioned.erase atom slot tagged lookup field (fallback.clauseFan, fallback.group)
  change (presentedIncidenceIndexFields positioned
      (fun clauseIndex literalIndex =>
        (horizontalOccurrenceClauseRibbonFanDataComputed (source, clauseIndex),
          terminalGroupOfLiteralIndex literalIndex))).getD
      (occurrenceEntryIndex positioned.erase (atom, slot))
      (fallback.clauseFan, fallback.group) = field tagged at selected
  rw [← directSourceFinalClauseFrames_fan_groups_eq_normalized decider symbols] at selected
  rw [List.getD_map (directSourceFinalClauseFrames decider symbols) fallback
    (fun frame => (frame.clauseFan, frame.group))] at selected
  exact selected

end LeanTrominoes.PeriodicCNFStripReduction

end
