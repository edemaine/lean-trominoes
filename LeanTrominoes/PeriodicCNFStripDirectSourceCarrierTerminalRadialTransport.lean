/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierTerminalColumnData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFamilyStarts
import LeanTrominoes.RetainedAngularFinalRouteDecidableEqIrrelevance

/-! # Transport of direct carrier radial data to the width-three source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCarrierRadialTransportStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directCarrierRadialTransportVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Replacing the public final formula and equality implementation by the
raw five-family boundary leaves the carrier radial stream unchanged. -/
theorem directSourceCarrierTerminalRadialLengths_eq_raw
    (symbols : List encoding.Γ) :
    directSourceCarrierTerminalRadialLengths decider symbols =
      CarrierRankOrderedPairs.retainedTerminalRadialLengths
        (@PeriodicCNF.numericRouteDescriptors Variable
          PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
          (directSourceFinalNormalizedFormula decider symbols)) := by
  unfold directSourceCarrierTerminalRadialLengths
  calc
    CarrierRankOrderedPairs.retainedTerminalRadialLengths
          (@PeriodicCNF.numericRouteDescriptors Variable
            directSourceVariableDecidableEq
            (directSourceFormula decider symbols)) =
        CarrierRankOrderedPairs.retainedTerminalRadialLengths
          (@PeriodicCNF.numericRouteDescriptors Variable
            directSourceVariableDecidableEq
            (directSourceFinalNormalizedFormula decider symbols)) :=
      congrArg CarrierRankOrderedPairs.retainedTerminalRadialLengths
        (congrArg
          (@PeriodicCNF.numericRouteDescriptors Variable
            directSourceVariableDecidableEq)
          (directSourceFormula_eq_finalNormalized decider symbols))
    _ = _ :=
      congrArg CarrierRankOrderedPairs.retainedTerminalRadialLengths
        (numericRouteDescriptors_decidableEq_irrel
          directSourceVariableDecidableEq
          PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
          (directSourceFinalNormalizedFormula decider symbols))

end LeanTrominoes.PeriodicCNFStripReduction

end
