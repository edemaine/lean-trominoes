/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectFigureNineCycleRouteTailRecordCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFiveFamilyCompiledRecordCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFiveFamilyCompiledRecordSemantics
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2NativeListAppendClosure

/-! # Complete compiled direct Figure 9 route-tail records -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCompiledRouteTailRecordStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCompiledRouteTailRecordVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Expand the fixed implication-cycle clause records to header/tail records. -/
def directSourceFinalCycleCompiledBatchedRecords
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteHeaderTail.Token :=
  HorizontalRoutedRouteTailRecord.batchedRecords
    (directFigureNineCycleRouteTailRecordTokens decider symbols)

/-- Complete retained Figure 9 header/tail record stream: the five copied
families followed by the fixed implication-cycle suffix. -/
def directSourceFinalCompiledRouteTailRecords
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteHeaderTail.Token :=
  directSourceFinalFiveFamilyCompiledRecords decider symbols ++
    directSourceFinalCycleCompiledBatchedRecords decider symbols

/-- The cycle record compiler followed by bounded batch expansion is
polynomial-time. -/
noncomputable def
    directSourceFinalCycleCompiledBatchedRecordsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalCycleCompiledBatchedRecords decider) := by
  unfold directSourceFinalCycleCompiledBatchedRecords
  exact TM2CompositionMachine.computableInPolyTime
    (directFigureNineCycleRouteTailRecordTokensComputableInPolyTime decider)
    HorizontalRoutedRouteTailRecord.batchedRecordsComputableInPolyTime

/-- The complete direct Figure 9 header/tail record stream is
polynomial-time. -/
noncomputable def
    directSourceFinalCompiledRouteTailRecordsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalCompiledRouteTailRecords decider) := by
  unfold directSourceFinalCompiledRouteTailRecords
  exact TM2ListAppend.nativeComputableInPolyTime
    (directSourceFinalFiveFamilyCompiledRecordsComputableInPolyTime decider)
    (directSourceFinalCycleCompiledBatchedRecordsComputableInPolyTime decider)

/-- The complete compiled stream is exactly the canonical retained Figure 9
header/tail record list, including the implication cycles. -/
theorem directSourceFinalCompiledRouteTailRecords_eq
    (symbols : List encoding.Γ) :
    directSourceFinalCompiledRouteTailRecords decider symbols =
      directFigureNinePolarityRouteTailRecords decider symbols := by
  unfold directSourceFinalCompiledRouteTailRecords
    directSourceFinalCycleCompiledBatchedRecords
  rw [directSourceFinalFiveFamilyCompiledRecords_eq_copied,
    ← batchedRecords_directFigureNinePolarityRouteTailRecordTokens,
    directFigureNinePolarityRouteTailRecordTokens_eq_blocks,
    directFigureNineCopiedRouteTailRecordTokens_eq_fiveFamilies]
  simp only [
    batchedRecords_retainedFinalNormalizedClauseSemantic_append,
    List.append_assoc]

end LeanTrominoes.PeriodicCNFStripReduction

end
