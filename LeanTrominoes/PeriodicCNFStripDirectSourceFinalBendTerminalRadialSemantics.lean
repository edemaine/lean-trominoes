/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceBendTerminalRadialTransport
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendTerminalCoordinateTransport
import LeanTrominoes.PeriodicCNFStripDirectThreeCNFSourceFinalBendTerminalRadialSemantics
import LeanTrominoes.RetainedAngularOccurrenceTerminalCoordinateComponentData

/-! # Actual radial-column semantics of direct-source bends -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplit.TerminalCoordinateComponents

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendRadialSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalBendRadialSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The compiled base-bend radial lengths are the radial projection of the
actual bend-family coordinates. -/
theorem directSourceFinalBendTerminalRadialLengths_eq_actual
    (symbols : List encoding.Γ) :
    directSourceBaseBendTerminalRadialLengths decider symbols =
      radialLengths
        (retainedFinalTerminalCoordinatesFrom
          (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
            (directSourceFormula decider symbols))
          (directSourceFinalBendStart decider symbols)
          (directSourceFinalBendClauses decider symbols)) := by
  calc
    directSourceBaseBendTerminalRadialLengths decider symbols =
        @baseBendTerminalRadialLengths Variable
          PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
          (directSourceFinalNormalizedFormula decider symbols) :=
      directSourceBaseBendTerminalRadialLengths_eq_raw decider symbols
    _ = radialLengths
          (directThreeCNFSourceFinalBendActualCoordinates
            decider symbols) :=
      directThreeCNFSourceFinalBendTerminalRadialLengths_eq_actual
        decider symbols
    _ = radialLengths
          (retainedFinalTerminalCoordinatesFrom
            (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
              (directSourceFormula decider symbols))
            (directSourceFinalBendStart decider symbols)
            (directSourceFinalBendClauses decider symbols)) :=
      congrArg radialLengths
        (directSourceFinalBendActualCoordinates_eq_raw
          decider symbols).symm

end LeanTrominoes.PeriodicCNFStripReduction

end
