/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordClockwiseRelabelBatchSemantics
import LeanTrominoes.BinaryRouteTailRecordClockwiseRelabelCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendDecodedRecordSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendNormalizedFallbackCompiledRecordSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteTailRecordCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Compiled batched semantics of direct final bends -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendCompiledBatchedRecordStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

attribute [local implicit_reducible]
  directSourceFinalOriginalBaseDecidableEq
attribute [local instance]
  directSourceFinalOriginalBaseDecidableEq

local instance directFinalBendCompiledBatchedRecordVariableDecidableEq :
    DecidableEq Variable :=
  directSourceFinalOriginalVariableDecidableEq

/-- Complete compiled bend record phase: normalized block formatting,
clockwise source-slot relabeling, and batched routed-record expansion. -/
def directSourceFinalBendCompiledBatchedRecords
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteHeaderTail.Token :=
  HorizontalRoutedRouteTailRecord.batchedRecords
    (BinaryRouteTailRecordClockwiseRelabel.output
      (directSourceFinalBendNormalizedFallbackCompiledRouteTailRecordTokens
        decider symbols))

/-- Formatting the compiled normalized bend routes, relabeling them clockwise,
and expanding them in batches produces the batched semantic records of the
direct bend clauses. -/
theorem directSourceFinalBendCompiledBatchedRecords_eq_semantic
    (symbols : List encoding.Γ) :
    directSourceFinalBendCompiledBatchedRecords decider symbols =
      HorizontalRoutedRouteTailRecord.batchedRecords
        (retainedFinalNormalizedClauseSemanticRouteTailRecordTokens
          (directSourceFormula decider symbols)
          (directSourceFinalBendStart decider symbols)
          (directSourceFinalBendClauses decider symbols)) := by
  unfold directSourceFinalBendCompiledBatchedRecords
  rw [directSourceFinalBendNormalizedFallbackCompiledRouteTailRecordTokens_eq]
  unfold directSourceFinalBendNormalizedFallbackRouteTailRecordTokens
  rw [BinaryRouteTailRecordClockwiseRelabel.batchedRecords_output_batchFormatter_records]
  exact (directSourceFinalBendBatchedSemanticRecords_eq_decodedRecords
    decider symbols).symm

/-- The complete compiled bend record phase is polynomial-time. -/
noncomputable def
    directSourceFinalBendCompiledBatchedRecordsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalBendCompiledBatchedRecords decider) := by
  unfold directSourceFinalBendCompiledBatchedRecords
  exact TM2CompositionMachine.computableInPolyTime
    (TM2CompositionMachine.computableInPolyTime
      (directSourceFinalBendNormalizedFallbackCompiledRouteTailRecordTokensComputableInPolyTime
        decider)
      BinaryRouteTailRecordClockwiseRelabel.outputComputableInPolyTime)
    HorizontalRoutedRouteTailRecord.batchedRecordsComputableInPolyTime

end LeanTrominoes.PeriodicCNFStripReduction

end
