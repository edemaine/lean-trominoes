/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierFallbackSuffixOccurrenceLength
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierFallbackSuffixDirectionLength
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierFallbackSuffixRadialLength

/-! # Length alignment of carrier fallback-suffix query columns -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierFallbackQueryLengthStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierFallbackQueryLengthVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

theorem directSourceFinalCarrierFallbackRolesSlots_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCarrierFallbackHeaderRoles decider symbols).length =
      (directSourceFinalCarrierOccurrenceSlots decider symbols).length := by
  unfold directSourceFinalCarrierFallbackHeaderRoles
    directSourceFinalCarrierFallbackTerminalDirections
    RetainedTerminalDirectionRankDecoder.directionsOfRanks
  rw [FallbackSuffixHeaderRoles.carrierRoles_length]
  simp only [List.length_map]
  exact
    (directSourceFinalCarrierDirectionRanks_length_eq_coordinates
      decider symbols).trans
    (directSourceFinalCarrierOccurrenceSlots_length_eq_coordinates
      decider symbols).symm

theorem directSourceFinalCarrierFallbackRolesRadials_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCarrierFallbackHeaderRoles decider symbols).length =
      (directSourceCarrierTerminalRadialLengths decider symbols).length := by
  unfold directSourceFinalCarrierFallbackHeaderRoles
    directSourceFinalCarrierFallbackTerminalDirections
    RetainedTerminalDirectionRankDecoder.directionsOfRanks
  rw [FallbackSuffixHeaderRoles.carrierRoles_length]
  simp only [List.length_map]
  exact
    (directSourceFinalCarrierDirectionRanks_length_eq_coordinates
      decider symbols).trans
    (directSourceFinalCarrierRadialLengths_length_eq_coordinates
      decider symbols).symm

end LeanTrominoes.PeriodicCNFStripReduction

end
