/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedTerminalSlotCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderCopiedSourcePositionSemantics

/-! # Semantics of direct copied terminal slots -/

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- There is one selected terminal slot per direct copied final occurrence,
including harmless values in the parent-local positions. -/
theorem directSourceFinalCopiedTerminalSlotValues_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCopiedTerminalSlotValues decider symbols).length =
      (directSourceFinalCopiedOccurrenceData decider symbols).length := by
  unfold directSourceFinalCopiedTerminalSlotValues
    directSourceFinalCopiedOccurrenceData
  exact HorizontalRoutedRouteHeaderCopiedSourcePosition.selectedValues_length
    _ _

/-- Every copied terminal-slot value is ordinary zero-based lookup in the
pre-Figure9 slot column at the compiled presentation position. -/
theorem directSourceFinalCopiedTerminalSlotValues_eq_map_getD
    (symbols : List encoding.Γ) :
    directSourceFinalCopiedTerminalSlotValues decider symbols =
      (directSourceFinalCopiedSourcePositions decider symbols).map
        fun position =>
          (directSourceFinalTerminalSlotValues decider symbols).getD
            position 0 := by
  unfold directSourceFinalCopiedTerminalSlotValues
    directSourceFinalCopiedSourcePositions
  apply HorizontalRoutedRouteHeaderCopiedSourcePosition.selectedValues_eq_map_getD
  exact directSourceFinalTerminalSlotValues_length_eq_total decider symbols

end LeanTrominoes.PeriodicCNFStripReduction
