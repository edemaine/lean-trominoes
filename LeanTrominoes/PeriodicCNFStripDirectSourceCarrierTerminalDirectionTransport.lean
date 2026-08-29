/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierTerminalColumnData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFamilyStarts
import LeanTrominoes.RetainedAngularFinalRouteDecidableEqIrrelevance

/-! # Transport of direct carrier direction data to the width-three source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCarrierDirectionTransportStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directCarrierDirectionTransportVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Replacing the public final formula and equality implementation by the
raw five-family boundary leaves the carrier direction stream unchanged. -/
theorem directSourceCarrierTerminalDirectionRanks_eq_raw
    (symbols : List encoding.Γ) :
    directSourceCarrierTerminalDirectionRanks decider symbols =
      CarrierRankOrderedPairs.retainedTerminalDirectionRanks
        (@PeriodicCNF.numericRouteDescriptors Variable
          PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
          (directSourceFinalNormalizedFormula decider symbols)) := by
  unfold directSourceCarrierTerminalDirectionRanks
  calc
    CarrierRankOrderedPairs.retainedTerminalDirectionRanks
          (@PeriodicCNF.numericRouteDescriptors Variable
            directSourceVariableDecidableEq
            (directSourceFormula decider symbols)) =
        CarrierRankOrderedPairs.retainedTerminalDirectionRanks
          (@PeriodicCNF.numericRouteDescriptors Variable
            directSourceVariableDecidableEq
            (directSourceFinalNormalizedFormula decider symbols)) :=
      congrArg CarrierRankOrderedPairs.retainedTerminalDirectionRanks
        (congrArg
          (@PeriodicCNF.numericRouteDescriptors Variable
            directSourceVariableDecidableEq)
          (directSourceFormula_eq_finalNormalized decider symbols))
    _ = _ :=
      congrArg CarrierRankOrderedPairs.retainedTerminalDirectionRanks
        (numericRouteDescriptors_decidableEq_irrel
          directSourceVariableDecidableEq
          PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
          (directSourceFinalNormalizedFormula decider symbols))

end LeanTrominoes.PeriodicCNFStripReduction

end
