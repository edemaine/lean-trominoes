/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanHorizontalSemantics

/-! # Polynomial-time emission in the canonical horizontal occurrence order -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance groupedFanCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

/-- Actual complete horizontal variable fans paired with their active slots,
in the canonical normalized source occurrence-entry order. -/
def directSourceFinalHorizontalGroupedVariableFanSlots
    (symbols : List encoding.Γ) : List GroupedVariableFanSlot :=
  (occurrenceEntries (horizontalSemanticNormalizedRibbonSource
    (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase).map
    (fun entry =>
      (horizontalOccurrenceVariableRibbonFanDataComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols, entry.1),
      groupedVariableFanGenericSlot entry.2))

/-- The actual grouped fan/slot stream has a uniform polynomial-time
compiler with exact source-order agreement already proved. -/
noncomputable def directSourceFinalHorizontalGroupedVariableFanSlotsComputableInPolyTime :
    TM2ComputableInPolyTime id id (directSourceFinalHorizontalGroupedVariableFanSlots decider) := by
  apply TM2ComputableInPolyTime.of_eq
    (directSourceFinalGroupedVariableFanSlotsComputableInPolyTime decider)
  intro symbols
  exact directSourceFinalGroupedVariableFanSlots_eq_horizontal decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
