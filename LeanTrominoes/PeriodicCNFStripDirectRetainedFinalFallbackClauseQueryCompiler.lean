/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryTemplateCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalFallbackClauseQueryData
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCarrierClauseDescriptorCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataBaseBendClauseDescriptorCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Compiling direct final fallback-family clause queries -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalFallbackQueryCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Compose the retained carrier descriptor compiler with the identity query
wrapper. -/
noncomputable def
    directRetainedFinalCarrierClauseQueriesComputableInPolyTime :
    DirectRetainedFinalCarrierClauseQueryCompiler decider := by
  let descriptors :=
    directRetainedPlanarMetadataCarrierClauseDescriptorsComputableInPolyTime
      decider
  let queries := retainedFinalPrecomputedClauseQueriesComputableInPolyTime
  let complete :=
    TM2CompositionMachine.computableInPolyTime descriptors queries
  change @TM2ComputableInPolyTime
    (List encoding.Γ) (List RetainedFinalCopiedClauseQuery)
    encoding.Γ RetainedFinalCopiedClauseQuery id id
    (fun symbols => retainedFinalPrecomputedClauseQueries
      (directRetainedPlanarMetadataCarrierClauseDescriptors decider symbols))
  exact complete

/-- Compose the normalized retained-bend descriptor compiler with the
identity query wrapper. -/
noncomputable def
    directRetainedFinalBendClauseQueriesComputableInPolyTime :
    DirectRetainedFinalBendClauseQueryCompiler decider := by
  let descriptors :=
    directRetainedPlanarMetadataBaseBendClauseDescriptorsComputableInPolyTime
      decider
  let queries := retainedFinalPrecomputedClauseQueriesComputableInPolyTime
  let complete :=
    TM2CompositionMachine.computableInPolyTime descriptors queries
  change @TM2ComputableInPolyTime
    (List encoding.Γ) (List RetainedFinalCopiedClauseQuery)
    encoding.Γ RetainedFinalCopiedClauseQuery id id
    (fun symbols => retainedFinalPrecomputedClauseQueries
      (directRetainedPlanarMetadataBaseBendClauseDescriptors decider symbols))
  exact complete

end LeanTrominoes.PeriodicCNFStripReduction

end
