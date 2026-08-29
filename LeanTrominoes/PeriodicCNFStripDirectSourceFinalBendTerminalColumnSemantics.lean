/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceBendTerminalDirectionTransport
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendTerminalCoordinateTransport
import LeanTrominoes.PeriodicCNFStripDirectThreeCNFSourceFinalBendTerminalDirectionSemantics
import LeanTrominoes.RetainedAngularOccurrenceTerminalCoordinateComponentData

/-! # Actual direction-column semantics of direct-source bends -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplit.TerminalCoordinateComponents

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendDirectionSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

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
