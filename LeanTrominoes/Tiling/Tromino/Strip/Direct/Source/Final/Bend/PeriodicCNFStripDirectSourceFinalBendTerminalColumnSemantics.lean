/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Bend.PeriodicCNFStripDirectSourceBendTerminalDirectionTransport
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Bend.PeriodicCNFStripDirectSourceFinalBendTerminalCoordinateTransport
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectThreeCNFSourceFinalBendTerminalDirectionSemantics
import LeanTrominoes.SAT.Planar.OccurrenceSplit.RetainedAngularOccurrenceTerminalCoordinateComponentData

/-! # Actual direction-column semantics of direct-source bends -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplit.TerminalCoordinateComponents

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directFinalBendDirectionSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The compiled base-bend direction ranks are the direction projection of
the actual bend-family coordinates. -/
theorem directSourceFinalBendTerminalDirectionRanks_eq_actual
    (symbols : List encoding.Γ) :
    directSourceBaseBendTerminalDirectionRanks decider symbols =
      directionRanks
        (retainedFinalTerminalCoordinatesFrom
          (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
            (directSourceFormula decider symbols))
          (directSourceFinalBendStart decider symbols)
          (directSourceFinalBendClauses decider symbols)) := by
  calc
    directSourceBaseBendTerminalDirectionRanks decider symbols =
        @baseBendTerminalDirectionRanks Variable
          PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
          (directSourceFinalNormalizedFormula decider symbols) :=
      directSourceBaseBendTerminalDirectionRanks_eq_raw decider symbols
    _ = directionRanks
          (directThreeCNFSourceFinalBendActualCoordinates
            decider symbols) :=
      directThreeCNFSourceFinalBendTerminalDirectionRanks_eq_actual
        decider symbols
    _ = directionRanks
          (retainedFinalTerminalCoordinatesFrom
            (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
              (directSourceFormula decider symbols))
            (directSourceFinalBendStart decider symbols)
            (directSourceFinalBendClauses decider symbols)) :=
      congrArg directionRanks
        (directSourceFinalBendActualCoordinates_eq_raw
          decider symbols).symm

end LeanTrominoes.PeriodicCNFStripReduction

end
