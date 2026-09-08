/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFanRankLookup
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceFieldsHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceFieldLookup
import LeanTrominoes.FiniteAlphabetKeyedValueLookupUniqueSemantics

/-! # Compiled fan queries select actual source occurrence fields -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PlanarThreeDM PeriodicOneInThreeToThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance fanFieldLookupStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

/-- The finite record selected by a genuine fan query contains the kind,
polarity, and variable-end direction of that exact actual source occurrence. -/
theorem directSourceFinalFanOccurrence_fields_of_occurrenceAt
    (symbols : List encoding.Γ) (index : Nat) (atom : RoutedVariable)
    (atomLookup : (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences[index]? = some atom)
    (slot : OccurrenceSlot) (tagged : TaggedOccurrence RoutedVariable)
    (occurrenceLookup : occurrenceAt (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase atom slot = some tagged) :
    let record : HorizontalRoutedRouteHeader.OccurrenceData := FiniteAlphabetKeyedValueLookup.alignedDatum
      (directSourceFinalOccurrenceCandidateKeys decider symbols)
      (directSourceFinalVariableOccurrenceData decider symbols)
      ((directSourceFinalAtomIdentityCodes decider symbols).getD index 0 * 3 + slot.index)
    ((record.kind, record.polarity), record.direction) =
      taggedPresentedOccurrenceFields
        (horizontalSemanticNormalizedPlanarPresentation
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).routes tagged := by
  let positioned := horizontalSemanticNormalizedRibbonSource
    (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)
  let routes := (horizontalSemanticNormalizedPlanarPresentation
    (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).routes
  let records := directSourceFinalVariableOccurrenceData decider symbols
  let field := fun record : HorizontalRoutedRouteHeader.OccurrenceData =>
    ((record.kind, record.polarity), record.direction)
  have filteredLookup : (occurrencesOf positioned.erase atom)[slot.index]? = some tagged := occurrenceLookup
  have rankLt : slot.index < positioned.erase.variableOccurrences.count atom := by
    have valid := (List.getElem?_eq_some_iff.mp filteredLookup).1
    simpa only [occurrencesOf_length, List.count_eq_countP, Bool.beq_eq_decide_eq] using valid
  have selectedIndex := directSourceFinalOccurrenceCandidateKeys_idxOf_rank_normalized
    decider symbols index atom atomLookup slot.index rankLt
  have fieldsEq : records.map field = presentedOccurrenceFields positioned routes :=
    directSourceFinalVariableOccurrenceData_fields_eq_normalized decider symbols
  have selectedFields := presentedOccurrenceFields_getD_of_occurrenceAt
    positioned routes atom slot tagged occurrenceLookup (field default)
  change field (records.getD
    ((directSourceFinalOccurrenceCandidateKeys decider symbols).idxOf
      ((directSourceFinalAtomIdentityCodes decider symbols).getD index 0 * 3 + slot.index)) default) = _
  rw [selectedIndex, ← List.getD_map records default field, fieldsEq]
  simpa only [List.idxsOf, Bool.beq_eq_decide_eq] using selectedFields

end LeanTrominoes.PeriodicCNFStripReduction

end
