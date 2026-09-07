/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceFieldsHorizontalSemantics

/-! # Polynomial-time emission of the normalized occurrence fields -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PlanarThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

local instance normalizedOccurrenceFieldsInhabited :
    Inhabited ((VariableConnectorKind × Bool) × AxisDirection) :=
  ⟨((.fixedRed, false), .north)⟩

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance normalizedOccurrenceFieldsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The kind, polarity, and endpoint direction of each actual normalized
horizontal occurrence, before regrouping by variable. -/
def directSourceFinalNormalizedOccurrenceFields (symbols : List encoding.Γ) :
    List ((VariableConnectorKind × Bool) × AxisDirection) :=
  presentedOccurrenceFields
    (horizontalSemanticNormalizedRibbonSource (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))
    (horizontalSemanticNormalizedPlanarPresentation
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).routes

/-- The completed direct occurrence compiler emits exactly these semantic
fields in polynomial time, with all three fields aligned to the same incidence. -/
noncomputable def directSourceFinalNormalizedOccurrenceFieldsComputableInPolyTime :
    TM2ComputableInPolyTime id id (directSourceFinalNormalizedOccurrenceFields decider) := by
  let compiled := TM2CompositionMachine.computableInPolyTime
    (directSourceFinalVariableOccurrenceDataComputableInPolyTime decider)
    (FiniteBlockTransducer.computableInPolyTime
      (fun record : HorizontalRoutedRouteHeader.OccurrenceData =>
        [((record.kind, record.polarity), record.direction)]))
  apply Turing.TM2ComputableInPolyTime.of_eq compiled
  intro symbols
  rw [← List.map_eq_flatMap]
  exact directSourceFinalVariableOccurrenceData_fields_eq_normalized decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
