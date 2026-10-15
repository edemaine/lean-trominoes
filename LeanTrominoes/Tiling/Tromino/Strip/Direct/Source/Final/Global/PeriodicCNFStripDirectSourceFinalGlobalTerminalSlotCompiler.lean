/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Global.PeriodicCNFStripDirectSourceFinalGlobalStableRankCompiler
import LeanTrominoes.Computation.TM2.TM2CompositionMachine
import LeanTrominoes.Computation.Encoding.Unary.UnaryFieldBoundedRetainedTerminalSlotCompiler

/-! # Compiler for final global bounded terminal slots -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


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
