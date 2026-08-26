/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalFallbackClauseQueryData

/-! # Semantics of final fallback-family clause queries -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalFallbackQuerySemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Evaluating the retained-carrier wrapper queries recovers their
already-final metadata descriptors. -/
theorem directRetainedFinalCarrierClauseQueryDescriptors_eq
    (symbols : List encoding.Γ) :
    retainedFinalCopiedClauseDescriptors
        (directRetainedFinalCarrierClauseQueries decider symbols) =
      directRetainedPlanarMetadataCarrierClauseDescriptors
        decider symbols := by
  unfold directRetainedFinalCarrierClauseQueries
  exact retainedFinalCopiedClauseDescriptors_precomputed _

/-- Evaluating the retained-bend wrapper queries recovers their
already-final metadata descriptors. -/
theorem directRetainedFinalBendClauseQueryDescriptors_eq
    (symbols : List encoding.Γ) :
    retainedFinalCopiedClauseDescriptors
        (directRetainedFinalBendClauseQueries decider symbols) =
      directRetainedPlanarMetadataBaseBendClauseDescriptors
        decider symbols := by
  unfold directRetainedFinalBendClauseQueries
  exact retainedFinalCopiedClauseDescriptors_precomputed _

end LeanTrominoes.PeriodicCNFStripReduction

end
