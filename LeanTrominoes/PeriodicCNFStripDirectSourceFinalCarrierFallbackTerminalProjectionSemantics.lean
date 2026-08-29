/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierFallbackTerminalDataPresentation
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackSuffixQueryData

/-! # Direction and radial projections of carrier fallback terminal data -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierFallbackTerminalProjectionStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierFallbackTerminalProjectionVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

theorem directSourceFinalCarrierFallbackTerminalDirections_eq
    (symbols : List encoding.Γ) :
    directSourceFinalCarrierFallbackTerminalDirections decider symbols =
      (directSourceFinalCarrierFallbackTerminalData
        decider symbols).map Prod.fst := by
  rw [directSourceFinalCarrierFallbackTerminalData_eq_blocks]
  unfold directSourceFinalCarrierFallbackTerminalDirections
    directSourceCarrierTerminalDirectionRanks
    RetainedTerminalDirectionRankDecoder.directionsOfRanks
    CarrierRankOrderedPairs.retainedTerminalDirectionRanks
    terminalDataDirectionRanks
  simp [Function.comp_def]

theorem directSourceFinalCarrierFallbackTerminalRadialLengths_eq
    (symbols : List encoding.Γ) :
    directSourceCarrierTerminalRadialLengths decider symbols =
      (directSourceFinalCarrierFallbackTerminalData
        decider symbols).map Prod.snd := by
  rw [directSourceFinalCarrierFallbackTerminalData_eq_blocks]
  unfold directSourceCarrierTerminalRadialLengths
    CarrierRankOrderedPairs.retainedTerminalRadialLengths
    terminalDataRadialLengths
  simp

end LeanTrominoes.PeriodicCNFStripReduction

end
