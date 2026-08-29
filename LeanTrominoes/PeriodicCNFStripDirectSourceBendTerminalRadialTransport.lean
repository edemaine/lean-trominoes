/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceBaseBendTerminalColumnData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFamilyStarts
import LeanTrominoes.RetainedAngularBendTerminalCoordinateData
import LeanTrominoes.RetainedAngularFinalRouteDecidableEqIrrelevance

/-! # Transport of direct bend radial data to the width-three source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directBendRadialTransportStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directBendRadialTransportVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Replacing the public final formula and equality implementation by the
raw five-family boundary leaves the bend radial stream unchanged. -/
theorem directSourceBaseBendTerminalRadialLengths_eq_raw
    (symbols : List encoding.Γ) :
    directSourceBaseBendTerminalRadialLengths decider symbols =
      @baseBendTerminalRadialLengths Variable
        PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
        (directSourceFinalNormalizedFormula decider symbols) := by
  change @baseBendTerminalRadialLengths Variable
      directSourceVariableDecidableEq
      (directSourceFormula decider symbols) = _
  calc
    @baseBendTerminalRadialLengths Variable
          directSourceVariableDecidableEq
          (directSourceFormula decider symbols) =
        @baseBendTerminalRadialLengths Variable
          directSourceVariableDecidableEq
          (directSourceFinalNormalizedFormula decider symbols) :=
      congrArg
        (@baseBendTerminalRadialLengths Variable
          directSourceVariableDecidableEq)
        (directSourceFormula_eq_finalNormalized decider symbols)
    _ = _ :=
      decidableEq_application_irrel
        (fun decEq : DecidableEq Variable =>
          @baseBendTerminalRadialLengths Variable decEq
            (directSourceFinalNormalizedFormula decider symbols))
        directSourceVariableDecidableEq
        PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq

end LeanTrominoes.PeriodicCNFStripReduction

end
