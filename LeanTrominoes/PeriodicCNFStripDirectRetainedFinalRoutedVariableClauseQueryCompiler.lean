/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalRoutedVariableClauseQueryData
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataNormalizedRoutedVariableDescriptorCompiler
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataNormalizedRoutedVariableDescriptorQuotient
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.RetainedInputAppendPipeline
import LeanTrominoes.TM2CompositionMachine

/-! # Compiling direct final routed-variable clause queries -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRoutedVariableQueryCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The elementwise stable-query replacement of the already-compiled
normalized routed-variable stream is polynomial time. -/
noncomputable def
    directRetainedFinalCompiledRoutedVariableClauseQueriesComputableInPolyTime :
    DirectRetainedFinalCompiledRoutedVariableClauseQueryCompiler decider := by
  let descriptors :=
    directRetainedPlanarMetadataNormalizedRoutedVariableClauseDescriptorsComputableInPolyTime
      decider
  let queries := FiniteBlockTransducer.computableInPolyTime
    retainedFinalDirectRoutedVariableQueryBlock
  let complete :=
    TM2CompositionMachine.computableInPolyTime descriptors queries
  change @TM2ComputableInPolyTime
    (List encoding.Γ) (List RetainedFinalCopiedClauseQuery)
    encoding.Γ RetainedFinalCopiedClauseQuery id id
    (fun symbols =>
      (directRetainedPlanarMetadataNormalizedRoutedVariableClauseDescriptors
        decider symbols).flatMap
          retainedFinalDirectRoutedVariableQueryBlock)
  exact complete

/-- The compiled replacement stream is exactly one stable site block per
source literal. -/
theorem directRetainedFinalCompiledRoutedVariableClauseQueries_eq
    (symbols : List encoding.Γ) :
    directRetainedFinalCompiledRoutedVariableClauseQueries decider symbols =
      directRetainedFinalRoutedVariableClauseQueries decider symbols := by
  unfold directRetainedFinalCompiledRoutedVariableClauseQueries
    directRetainedFinalRoutedVariableClauseQueries
  rw [directRetainedPlanarMetadataNormalizedRoutedVariableClauseDescriptors_eq_fullSites]
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro targetIndex _targetIndexMember
  exact routedVariableFullSiteBlock_finalQueryBlock_eq

/-- Hence the exact normalized final routed-variable query stream is
polynomial-time computable. -/
noncomputable def
    directRetainedFinalRoutedVariableClauseQueriesComputableInPolyTime :
    DirectRetainedFinalRoutedVariableClauseQueryCompiler decider :=
  RetainedInputAppendPipeline.computableInPolyTimeOfEq
    (directRetainedFinalCompiledRoutedVariableClauseQueries decider)
    (directRetainedFinalRoutedVariableClauseQueries decider)
    (directRetainedFinalCompiledRoutedVariableClauseQueries_eq decider)
    (directRetainedFinalCompiledRoutedVariableClauseQueriesComputableInPolyTime
      decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
