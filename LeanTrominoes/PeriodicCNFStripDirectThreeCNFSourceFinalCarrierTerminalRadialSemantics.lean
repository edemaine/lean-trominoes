/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectThreeCNFSourceFinalCarrierTerminalCoordinatesSemantics
import LeanTrominoes.RetainedAngularCarrierTerminalCoordinateProjectionSemantics

/-! # Radial projection of direct width-three carrier coordinates -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplit.TerminalCoordinateComponents
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directThreeCarrierRadialStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directThreeCarrierRadialOccurrenceDecidableEq :
    DecidableEq (ThreeOccurrenceVariable (ThreeCNFVariable Nat)) :=
  PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- The raw width-three carrier compiler lengths are the radial projection
of the actual final carrier coordinates. -/
theorem directThreeCNFSourceFinalCarrierTerminalRadialLengths_eq_actual
    (symbols : List encoding.Γ) :
    CarrierRankOrderedPairs.retainedTerminalRadialLengths
        (PeriodicCNF.numericRouteDescriptors
          (PeriodicThreeSATThree.formula
            (directThreeCNFSourceFormula decider symbols))) =
      radialLengths
        (directThreeCNFSourceFinalCarrierActualCoordinates
          decider symbols) := by
  have coordinateEq :=
    directThreeCNFSourceFinalCarrierTerminalCoordinates_eq_numeric
      decider symbols
  have radialEq := congrArg radialLengths coordinateEq
  unfold directThreeCNFSourceCarrierCompiledCoordinates at radialEq
  dsimp only at radialEq
  rw [PeriodicEightOccurrenceSplit.carrierTerminalCoordinates_radialLengths]
    at radialEq
  exact radialEq

end LeanTrominoes.PeriodicCNFStripReduction

end
