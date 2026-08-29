/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierFallbackPrefixSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierFallbackTerminalDataBlockStreamSemantics

/-! # Presentation of direct-source retained-carrier terminal data -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierFallbackTerminalPresentationStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierFallbackTerminalPresentationVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Compiler-ordered semantic terminal data of all retained carriers. -/
def directSourceFinalCarrierFallbackTerminalData
    (symbols : List encoding.Γ) : List RetainedTerminalData :=
  CarrierFallbackTerminalData.terminalData
    (directSourceFinalCarrierFallbackEntries decider symbols)

/-- The explicit retained-pair presentation agrees with the established
terminal-data block stream. -/
theorem directSourceFinalCarrierFallbackTerminalData_eq_blocks
    (symbols : List encoding.Γ) :
    directSourceFinalCarrierFallbackTerminalData decider symbols =
      (CarrierRankOrderedPairs.retainedTerminalDataBlocks
        (numericRouteDescriptors
          (directSourceFormula decider symbols))).flatten := by
  unfold directSourceFinalCarrierFallbackTerminalData
  rw [CarrierFallbackTerminalData.terminalData_eq_selectedTerminalDataBlocks]
  congr 1

end LeanTrominoes.PeriodicCNFStripReduction

end
