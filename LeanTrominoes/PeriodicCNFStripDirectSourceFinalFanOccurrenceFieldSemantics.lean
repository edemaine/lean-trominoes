/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFanOccurrenceFieldLookup
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceFieldSemantics

/-! # Complete semantic fields of every active direct variable-fan query -/

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

noncomputable local instance fanSemanticFieldsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

/-- Every active fan query returns the connector, polarity, and outgoing
route direction of that same semantic source occurrence. -/
theorem directSourceFinalFanOccurrence_fields_eq_semantic
    (symbols : List encoding.Γ) (index : Nat)
    (entry : ActiveOccurrenceEntry (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase)
    (atomLookup : (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences[index]? = some entry.1.1) :
    let record : HorizontalRoutedRouteHeader.OccurrenceData := FiniteAlphabetKeyedValueLookup.alignedDatum
      (directSourceFinalOccurrenceCandidateKeys decider symbols)
      (directSourceFinalVariableOccurrenceData decider symbols)
      ((directSourceFinalAtomIdentityCodes decider symbols).getD index 0 * 3 + entry.1.2.index)
    ((record.kind, record.polarity), record.direction) =
      ((occurrenceConnectorKind (horizontalSemanticNormalizedRibbonSource
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry.1.1 entry.1.2,
        occurrencePolarity (horizontalSemanticNormalizedRibbonSource
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase entry.1.1 entry.1.2),
        occurrenceSourceVariableDirection (horizontalSemanticNormalizedPlanarPresentation
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)) entry) := by
  let presentation := horizontalSemanticNormalizedPlanarPresentation
    (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)
  let data := occurrenceSpliceData presentation entry
  have selected := directSourceFinalFanOccurrence_fields_of_occurrenceAt
    decider symbols index entry.1.1 atomLookup entry.1.2 data.tagged data.occurrenceLookup
  exact selected.trans (taggedPresentedOccurrenceFields_eq_semantic
    presentation entry data.tagged data.occurrenceLookup)

end LeanTrominoes.PeriodicCNFStripReduction

end
