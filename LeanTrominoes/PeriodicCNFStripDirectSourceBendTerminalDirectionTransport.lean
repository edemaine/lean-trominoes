/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceBaseBendTerminalColumnData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFamilyStarts
import LeanTrominoes.RetainedAngularBendTerminalCoordinateData
import LeanTrominoes.RetainedAngularFinalRouteDecidableEqIrrelevance

/-! # Transport of direct bend direction data to the width-three source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directBendDirectionTransportStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directBendDirectionTransportVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Replacing the public final formula and equality implementation by the
raw five-family boundary leaves the bend direction stream unchanged. -/
theorem directSourceBaseBendTerminalDirectionRanks_eq_raw
    (symbols : List encoding.Γ) :
    directSourceBaseBendTerminalDirectionRanks decider symbols =
      @baseBendTerminalDirectionRanks Variable
        PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
        (directSourceFinalNormalizedFormula decider symbols) := by
  change @baseBendTerminalDirectionRanks Variable
      directSourceVariableDecidableEq
      (directSourceFormula decider symbols) = _
  calc
    @baseBendTerminalDirectionRanks Variable
          directSourceVariableDecidableEq
          (directSourceFormula decider symbols) =
        @baseBendTerminalDirectionRanks Variable
          directSourceVariableDecidableEq
          (directSourceFinalNormalizedFormula decider symbols) :=
      congrArg
        (@baseBendTerminalDirectionRanks Variable
          directSourceVariableDecidableEq)
        (directSourceFormula_eq_finalNormalized decider symbols)
    _ = _ :=
      decidableEq_application_irrel
        (fun decEq : DecidableEq Variable =>
          @baseBendTerminalDirectionRanks Variable decEq
            (directSourceFinalNormalizedFormula decider symbols))
        directSourceVariableDecidableEq
        PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq

end LeanTrominoes.PeriodicCNFStripReduction

end
