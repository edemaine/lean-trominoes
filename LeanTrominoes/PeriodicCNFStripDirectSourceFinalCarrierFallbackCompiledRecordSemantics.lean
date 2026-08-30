/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierFallbackRecordRouteSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierFallbackRecordProfileSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackRouteTailRecordCompiler

/-! # Semantics of compiled carrier fallback records -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierCompiledRecordStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Profile framing and complete carrier route compilation reconstruct the
exact declarative batch-formatter input. -/
theorem directSourceFinalCarrierFallbackCompiledRecordInputTokens_eq
    (symbols : List encoding.Γ) :
    directSourceFinalCarrierFallbackCompiledRecordInputTokens
        decider symbols =
      directSourceFinalCarrierFallbackRecordInputTokens
        decider symbols := by
  unfold directSourceFinalCarrierFallbackCompiledRecordInputTokens
    directSourceFinalCarrierFallbackRecordInputTokens
  rw [directSourceFinalCarrierFallbackCompiledRecordProfiles_eq,
    directSourceFinalCarrierFallbackRouteDirections_eq_blockRoutes]
  exact BinaryRouteTailRecordProfileFraming.framed_blockProfiles_blockRoutes _

/-- Consequently the polynomial-time carrier compiler emits the exact
declarative final fallback record stream. -/
theorem directSourceFinalCarrierFallbackCompiledRouteTailRecordTokens_eq
    (symbols : List encoding.Γ) :
    directSourceFinalCarrierFallbackCompiledRouteTailRecordTokens
        decider symbols =
      directSourceFinalCarrierFallbackRouteTailRecordTokens
        decider symbols := by
  unfold directSourceFinalCarrierFallbackCompiledRouteTailRecordTokens
  rw [directSourceFinalCarrierFallbackCompiledRecordInputTokens_eq,
    directSourceFinalCarrierFallbackRecordFormatter_output]

end LeanTrominoes.PeriodicCNFStripReduction

end
