/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGlobalStableRankCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.UnaryFieldBoundedRetainedTerminalSlotCompiler

/-! # Compiler for final global bounded terminal slots -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalGlobalTerminalSlotStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalGlobalTerminalSlotVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Bounding the compiled global stable ranks yields the exact global stream
of eight-way terminal slots used by direct Figure 9 clause records. -/
noncomputable def
    directSourceFinalGlobalTerminalSlotsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List RetainedTerminalSlot)
      encoding.Γ RetainedTerminalSlot id id
      (fun symbols =>
        BoundedRetainedTerminalSlots.slots
          (retainedOccurrenceGlobalStableTerminalRanks
            (retainedFinalCoordinatedScaledSource
              (directSourceFormula decider symbols)).erase
            (retainedFinalCoordinatedScaledSourceRoutes
              (directSourceFormula decider symbols)))) :=
  TM2CompositionMachine.computableInPolyTime
    (directSourceFinalGlobalStableTerminalRanksComputableInPolyTime decider)
    BoundedRetainedTerminalSlots.computableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end
