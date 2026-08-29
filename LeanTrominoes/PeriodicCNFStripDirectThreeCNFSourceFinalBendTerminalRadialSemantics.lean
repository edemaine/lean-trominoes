/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectThreeCNFSourceFinalBendTerminalCoordinatesSemantics
import LeanTrominoes.RetainedAngularBendTerminalCoordinateProjectionSemantics

/-! # Radial projection of direct width-three bend coordinates -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplit.TerminalCoordinateComponents

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directThreeBendRadialStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directThreeBendRadialOccurrenceDecidableEq :
    DecidableEq (ThreeOccurrenceVariable (ThreeCNFVariable Nat)) :=
  PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- The raw width-three bend compiler lengths are the radial projection of
the actual final bend coordinates. -/
theorem directThreeCNFSourceFinalBendTerminalRadialLengths_eq_actual
    (symbols : List encoding.Γ) :
    baseBendTerminalRadialLengths
        (PeriodicThreeSATThree.formula
          (directThreeCNFSourceFormula decider symbols)) =
      radialLengths
        (directThreeCNFSourceFinalBendActualCoordinates
          decider symbols) := by
  have coordinateEq :=
    directThreeCNFSourceFinalBendTerminalCoordinates_eq_numeric
      decider symbols
  have radialEq := congrArg radialLengths coordinateEq
  unfold directThreeCNFSourceBendCompiledCoordinates at radialEq
  dsimp only at radialEq
  rw [baseBendTerminalCoordinates_radialLengths] at radialEq
  exact radialEq

end LeanTrominoes.PeriodicCNFStripReduction

end
