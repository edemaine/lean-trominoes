/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendFallbackRecordRouteSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendFallbackRecordProfileSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackRouteTailRecordCompiler

/-! # Semantics of compiled bend fallback records -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendCompiledRecordStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

theorem directSourceFinalBendFallbackCompiledRecordInputTokens_eq
    (symbols : List encoding.Γ) :
    directSourceFinalBendFallbackCompiledRecordInputTokens decider symbols =
      directSourceFinalBendFallbackRecordInputTokens decider symbols := by
  unfold directSourceFinalBendFallbackCompiledRecordInputTokens
    directSourceFinalBendFallbackRecordInputTokens
  rw [directSourceFinalBendFallbackCompiledRecordProfiles_eq,
    directSourceFinalBendFallbackRouteDirections_eq_blockRoutes]
  exact BinaryRouteTailRecordProfileFraming.framed_blockProfiles_blockRoutes _

theorem directSourceFinalBendFallbackCompiledRouteTailRecordTokens_eq
    (symbols : List encoding.Γ) :
    directSourceFinalBendFallbackCompiledRouteTailRecordTokens
        decider symbols =
      directSourceFinalBendFallbackRouteTailRecordTokens decider symbols := by
  unfold directSourceFinalBendFallbackCompiledRouteTailRecordTokens
  rw [directSourceFinalBendFallbackCompiledRecordInputTokens_eq,
    directSourceFinalBendFallbackRecordFormatter_output]

end LeanTrominoes.PeriodicCNFStripReduction

end
