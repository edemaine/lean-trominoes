/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalDeduplicatedClauseShape
import LeanTrominoes.RetainedAngularFanFinalCoordinatedSourceClauses
import LeanTrominoes.RetainedAngularOccurrenceGlobalStableRankSlotBlocks

/-! # Direct-source stable-rank slot-block data -/

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

noncomputable local instance directFinalSlotBlockDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalSlotBlockDataVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Global stable-rank slots grouped in final direct-source clause order. -/
def directSourceFinalStableRankSlotBlocks
    (symbols : List encoding.Γ) : List (List RetainedTerminalSlot) :=
  let formula := directSourceFormula decider symbols
  retainedOccurrenceGlobalStableTerminalSlotBlocks
    (retainedFinalCoordinatedScaledSource formula).erase
    (retainedFinalCoordinatedScaledSourceRoutes formula)

theorem directSourceFinalStableRankSlotBlocks_eq
    (symbols : List encoding.Γ) :
    directSourceFinalStableRankSlotBlocks decider symbols =
      retainedOccurrenceGlobalStableTerminalSlotBlocks
        (retainedFinalCoordinatedScaledSource
          (directSourceFormula decider symbols)).erase
        (retainedFinalCoordinatedScaledSourceRoutes
          (directSourceFormula decider symbols)) := by
  rfl

theorem directSourceFinalStableRankSlotBlocks_flatten
    (symbols : List encoding.Γ) :
    (directSourceFinalStableRankSlotBlocks decider symbols).flatten =
      BoundedRetainedTerminalSlots.slots
        (retainedOccurrenceGlobalStableTerminalRanks
          (retainedFinalCoordinatedScaledSource
            (directSourceFormula decider symbols)).erase
          (retainedFinalCoordinatedScaledSourceRoutes
            (directSourceFormula decider symbols))) := by
  rw [directSourceFinalStableRankSlotBlocks_eq]
  exact retainedOccurrenceGlobalStableTerminalSlotBlocks_flatten _ _

theorem directSourceFinalScaledClauses_eq
    (symbols : List encoding.Γ) :
    (retainedFinalCoordinatedScaledSource
      (directSourceFormula decider symbols)).erase.clauses =
      deduplicatedClauses (directSourceFormula decider symbols) := by
  unfold retainedFinalCoordinatedScaledSource
  rw [PositionedPeriodicCNF.erase_scale]
  exact finalCoordinatedSource_erase_clauses_eq
    (directSourceFormula decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
