/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectThreeCNFSourceFinalBendTerminalCoordinatesSemantics
import LeanTrominoes.RetainedAngularBendTerminalCoordinateProjectionSemantics

/-! # Direction projection of direct width-three bend coordinates -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplit.TerminalCoordinateComponents

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directThreeBendDirectionStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directThreeBendDirectionOccurrenceDecidableEq :
    DecidableEq (ThreeOccurrenceVariable (ThreeCNFVariable Nat)) :=
  PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- The raw width-three bend compiler ranks are the direction projection of
the actual final bend coordinates. -/
theorem directThreeCNFSourceFinalBendTerminalDirectionRanks_eq_actual
    (symbols : List encoding.Γ) :
    baseBendTerminalDirectionRanks
        (PeriodicThreeSATThree.formula
          (directThreeCNFSourceFormula decider symbols)) =
      directionRanks
        (directThreeCNFSourceFinalBendActualCoordinates
          decider symbols) := by
  have coordinateEq :=
    directThreeCNFSourceFinalBendTerminalCoordinates_eq_numeric
      decider symbols
  have directionEq := congrArg directionRanks coordinateEq
  unfold directThreeCNFSourceBendCompiledCoordinates at directionEq
  dsimp only at directionEq
  rw [baseBendTerminalCoordinates_directionRanks] at directionEq
  exact directionEq

end LeanTrominoes.PeriodicCNFStripReduction

end
