/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendFallbackSuffixOccurrenceLength
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendFallbackSuffixDirectionLength
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendFallbackSuffixRadialLength

/-! # Length alignment of bend fallback-suffix query columns -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendFallbackQueryLengthStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalBendFallbackQueryLengthVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

theorem directSourceFinalBendFallbackRolesSlots_length
    (symbols : List encoding.Γ) :
    (directSourceFinalBendFallbackHeaderRoles decider symbols).length =
      (directSourceFinalBendOccurrenceSlots decider symbols).length := by
  unfold directSourceFinalBendFallbackHeaderRoles
    directSourceFinalBendFallbackTerminalDirections
    RetainedTerminalDirectionRankDecoder.directionsOfRanks
  rw [FallbackSuffixHeaderRoles.bendRoles_length]
  simp only [List.length_map]
  exact
    (directSourceFinalBendDirectionRanks_length_eq_coordinates
      decider symbols).trans
    (directSourceFinalBendOccurrenceSlots_length_eq_coordinates
      decider symbols).symm

theorem directSourceFinalBendFallbackRolesRadials_length
    (symbols : List encoding.Γ) :
    (directSourceFinalBendFallbackHeaderRoles decider symbols).length =
      (directSourceBaseBendTerminalRadialLengths decider symbols).length := by
  unfold directSourceFinalBendFallbackHeaderRoles
    directSourceFinalBendFallbackTerminalDirections
    RetainedTerminalDirectionRankDecoder.directionsOfRanks
  rw [FallbackSuffixHeaderRoles.bendRoles_length]
  simp only [List.length_map]
  exact
    (directSourceFinalBendDirectionRanks_length_eq_coordinates
      decider symbols).trans
    (directSourceFinalBendRadialLengths_length_eq_coordinates
      decider symbols).symm

end LeanTrominoes.PeriodicCNFStripReduction

end
