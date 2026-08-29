/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierTerminalDirectionTransport
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierTerminalCoordinateTransport
import LeanTrominoes.PeriodicCNFStripDirectThreeCNFSourceFinalCarrierTerminalDirectionSemantics
import LeanTrominoes.RetainedAngularOccurrenceTerminalCoordinateComponentData

/-! # Actual terminal-column semantics of direct-source carriers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplit.TerminalCoordinateComponents

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierTerminalSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

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
