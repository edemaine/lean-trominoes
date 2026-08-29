/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierTerminalRadialTransport
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierTerminalCoordinateTransport
import LeanTrominoes.PeriodicCNFStripDirectThreeCNFSourceFinalCarrierTerminalRadialSemantics
import LeanTrominoes.RetainedAngularOccurrenceTerminalCoordinateComponentData

/-! # Actual radial-column semantics of direct-source carriers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplit.TerminalCoordinateComponents

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierRadialSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierRadialSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The compiled carrier radial lengths are the radial projection of the
actual carrier-family coordinates. -/
theorem directSourceFinalCarrierTerminalRadialLengths_eq_actual
    (symbols : List encoding.Γ) :
    directSourceCarrierTerminalRadialLengths decider symbols =
      radialLengths
        (retainedFinalTerminalCoordinatesFrom
          (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
            (directSourceFormula decider symbols))
          (directSourceFinalCarrierStart decider symbols)
          (directSourceFinalCarrierClauses decider symbols)) := by
  calc
    directSourceCarrierTerminalRadialLengths decider symbols =
        PeriodicOrthocrossing.CarrierRankOrderedPairs.retainedTerminalRadialLengths
          (@PeriodicCNF.numericRouteDescriptors Variable
            PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
            (directSourceFinalNormalizedFormula decider symbols)) :=
      directSourceCarrierTerminalRadialLengths_eq_raw decider symbols
    _ = radialLengths
          (directThreeCNFSourceFinalCarrierActualCoordinates
            decider symbols) :=
      directThreeCNFSourceFinalCarrierTerminalRadialLengths_eq_actual
        decider symbols
    _ = radialLengths
          (retainedFinalTerminalCoordinatesFrom
            (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
              (directSourceFormula decider symbols))
            (directSourceFinalCarrierStart decider symbols)
            (directSourceFinalCarrierClauses decider symbols)) :=
      congrArg radialLengths
        (directSourceFinalCarrierActualCoordinates_eq_raw
          decider symbols).symm

end LeanTrominoes.PeriodicCNFStripReduction

end
