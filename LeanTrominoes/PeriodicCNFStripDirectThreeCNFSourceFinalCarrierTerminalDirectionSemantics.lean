/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectThreeCNFSourceFinalCarrierTerminalCoordinatesSemantics
import LeanTrominoes.RetainedAngularCarrierTerminalCoordinateProjectionSemantics

/-! # Direction projection of direct width-three carrier coordinates -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplit.TerminalCoordinateComponents
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directThreeCarrierDirectionStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directThreeCarrierDirectionOccurrenceDecidableEq :
    DecidableEq (ThreeOccurrenceVariable (ThreeCNFVariable Nat)) :=
  PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- The raw width-three carrier compiler ranks are the direction projection
of the actual final carrier coordinates. -/
theorem directThreeCNFSourceFinalCarrierTerminalDirectionRanks_eq_actual
    (symbols : List encoding.Γ) :
    CarrierRankOrderedPairs.retainedTerminalDirectionRanks
        (PeriodicCNF.numericRouteDescriptors
          (PeriodicThreeSATThree.formula
            (directThreeCNFSourceFormula decider symbols))) =
      directionRanks
        (directThreeCNFSourceFinalCarrierActualCoordinates
          decider symbols) := by
  have coordinateEq :=
    directThreeCNFSourceFinalCarrierTerminalCoordinates_eq_numeric
      decider symbols
  have directionEq := congrArg directionRanks coordinateEq
  unfold directThreeCNFSourceCarrierCompiledCoordinates at directionEq
  dsimp only at directionEq
  rw [PeriodicEightOccurrenceSplit.carrierTerminalCoordinates_directionRanks]
    at directionEq
  exact directionEq

end LeanTrominoes.PeriodicCNFStripReduction

end
