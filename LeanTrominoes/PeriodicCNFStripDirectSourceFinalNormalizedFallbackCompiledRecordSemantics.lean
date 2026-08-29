/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendNormalizedFallbackRecordRouteSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierNormalizedFallbackRecordRouteSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackRouteTailRecordSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalNormalizedFallbackRouteTailRecordCompiler

/-! # Semantics of compiled normalized carrier and bend fallback records -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalNormalizedCompiledRecordStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The normalized carrier compiler reconstructs the exact declarative
batch-formatter input for the normalized carrier blocks. -/
theorem directSourceFinalCarrierNormalizedFallbackCompiledRecordInputTokens_eq
    (symbols : List encoding.Γ) :
    directSourceFinalCarrierNormalizedFallbackCompiledRecordInputTokens
        decider symbols =
      directSourceFinalCarrierNormalizedFallbackRecordInputTokens
        decider symbols := by
  unfold directSourceFinalCarrierNormalizedFallbackCompiledRecordInputTokens
    directSourceFinalCarrierNormalizedFallbackRecordInputTokens
  rw [directSourceFinalCarrierFallbackCompiledRecordProfiles_eq,
    directSourceFinalCarrierNormalizedFallbackRouteDirections_eq_blockRoutes,
    ← directSourceFinalCarrierNormalizedFallbackRecordBlockProfiles_eq]
  exact BinaryRouteTailRecordProfileFraming.framed_blockProfiles_blockRoutes _

/-- The normalized bend compiler reconstructs the exact declarative
batch-formatter input for the normalized bend blocks. -/
theorem directSourceFinalBendNormalizedFallbackCompiledRecordInputTokens_eq
    (symbols : List encoding.Γ) :
    directSourceFinalBendNormalizedFallbackCompiledRecordInputTokens
        decider symbols =
      directSourceFinalBendNormalizedFallbackRecordInputTokens
        decider symbols := by
  unfold directSourceFinalBendNormalizedFallbackCompiledRecordInputTokens
    directSourceFinalBendNormalizedFallbackRecordInputTokens
  rw [directSourceFinalBendFallbackCompiledRecordProfiles_eq,
    directSourceFinalBendNormalizedFallbackRouteDirections_eq_blockRoutes,
    ← directSourceFinalBendNormalizedFallbackRecordBlockProfiles_eq]
  exact BinaryRouteTailRecordProfileFraming.framed_blockProfiles_blockRoutes _

/-- Consequently the polynomial-time carrier compiler emits the exact
normalized declarative fallback record stream. -/
theorem directSourceFinalCarrierNormalizedFallbackCompiledRouteTailRecordTokens_eq
    (symbols : List encoding.Γ) :
    directSourceFinalCarrierNormalizedFallbackCompiledRouteTailRecordTokens
        decider symbols =
      directSourceFinalCarrierNormalizedFallbackRouteTailRecordTokens
        decider symbols := by
  unfold directSourceFinalCarrierNormalizedFallbackCompiledRouteTailRecordTokens
  rw [directSourceFinalCarrierNormalizedFallbackCompiledRecordInputTokens_eq,
    directSourceFinalCarrierNormalizedFallbackRecordFormatter_output]

/-- Consequently the polynomial-time bend compiler emits the exact normalized
declarative fallback record stream. -/
theorem directSourceFinalBendNormalizedFallbackCompiledRouteTailRecordTokens_eq
    (symbols : List encoding.Γ) :
    directSourceFinalBendNormalizedFallbackCompiledRouteTailRecordTokens
        decider symbols =
      directSourceFinalBendNormalizedFallbackRouteTailRecordTokens
        decider symbols := by
  unfold directSourceFinalBendNormalizedFallbackCompiledRouteTailRecordTokens
  rw [directSourceFinalBendNormalizedFallbackCompiledRecordInputTokens_eq,
    directSourceFinalBendNormalizedFallbackRecordFormatter_output]

end LeanTrominoes.PeriodicCNFStripReduction

end
