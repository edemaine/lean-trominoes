/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalStableRankSlotBlockData

/-! # Lengths of direct-source stable-rank slot blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalSlotBlockLengthStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalSlotBlockLengthVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

theorem directSourceFinalStableRankSlotBlocks_lengths
    (symbols : List encoding.Γ) :
    (directSourceFinalStableRankSlotBlocks decider symbols).map
        List.length =
      (deduplicatedClauses
        (directSourceFormula decider symbols)).map List.length := by
  rw [directSourceFinalStableRankSlotBlocks_eq]
  rw [retainedOccurrenceGlobalStableTerminalSlotBlocks_lengths]
  rw [directSourceFinalScaledClauses_eq decider symbols]

end LeanTrominoes.PeriodicCNFStripReduction

end
