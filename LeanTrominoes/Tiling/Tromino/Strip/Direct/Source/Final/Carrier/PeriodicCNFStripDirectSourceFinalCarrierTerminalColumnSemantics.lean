/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Carrier.PeriodicCNFStripDirectSourceCarrierTerminalDirectionTransport
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Carrier.PeriodicCNFStripDirectSourceFinalCarrierTerminalCoordinateTransport
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectThreeCNFSourceFinalCarrierTerminalDirectionSemantics
import LeanTrominoes.SAT.Planar.OccurrenceSplit.RetainedAngularOccurrenceTerminalCoordinateComponentData

/-! # Actual terminal-column semantics of direct-source carriers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplit.TerminalCoordinateComponents

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directFinalCarrierTerminalSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The compiled carrier direction ranks are the direction projection of the
actual carrier-family coordinates. -/
theorem directSourceFinalCarrierTerminalDirectionRanks_eq_actual
    (symbols : List encoding.Γ) :
    directSourceCarrierTerminalDirectionRanks decider symbols =
      directionRanks
        (retainedFinalTerminalCoordinatesFrom
          (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
            (directSourceFormula decider symbols))
          (directSourceFinalCarrierStart decider symbols)
          (directSourceFinalCarrierClauses decider symbols)) := by
  calc
    directSourceCarrierTerminalDirectionRanks decider symbols =
        PeriodicOrthocrossing.CarrierRankOrderedPairs.retainedTerminalDirectionRanks
          (@PeriodicCNF.numericRouteDescriptors Variable
            PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
            (directSourceFinalNormalizedFormula decider symbols)) :=
      directSourceCarrierTerminalDirectionRanks_eq_raw decider symbols
    _ = directionRanks
          (directThreeCNFSourceFinalCarrierActualCoordinates
            decider symbols) :=
      directThreeCNFSourceFinalCarrierTerminalDirectionRanks_eq_actual
        decider symbols
    _ = directionRanks
          (retainedFinalTerminalCoordinatesFrom
            (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
              (directSourceFormula decider symbols))
            (directSourceFinalCarrierStart decider symbols)
            (directSourceFinalCarrierClauses decider symbols)) :=
      congrArg directionRanks
        (directSourceFinalCarrierActualCoordinates_eq_raw
          decider symbols).symm

end LeanTrominoes.PeriodicCNFStripReduction

end
