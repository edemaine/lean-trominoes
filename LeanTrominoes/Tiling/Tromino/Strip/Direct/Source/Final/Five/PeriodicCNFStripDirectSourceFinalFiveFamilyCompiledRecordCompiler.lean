/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Five.PeriodicCNFStripDirectSourceFinalFiveFamilyCompiledRecordData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Phase.PeriodicCNFStripDirectSourceFinalPhaseRouteTailRecordCompiler
import LeanTrominoes.Computation.TM2.TM2CompositionMachine
import LeanTrominoes.Computation.TM2.TM2NativeListAppendClosure

/-! # Compiler for all five direct final routed-record families -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Crossover input records followed by bounded batch expansion compile in
polynomial time. -/
noncomputable def
    directSourceFinalCrossoverBatchedRecordsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalCrossoverBatchedRecords decider) := by
  unfold directSourceFinalCrossoverBatchedRecords
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalCrossoverRouteTailRecordTokensComputableInPolyTime
      decider)
    HorizontalRoutedRouteTailRecord.batchedRecordsComputableInPolyTime

/-- Both routed suffix families followed by bounded batch expansion compile
in polynomial time. -/
noncomputable def
    directSourceFinalRoutedBatchedRecordsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalRoutedBatchedRecords decider) := by
  unfold directSourceFinalRoutedBatchedRecords
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalRoutedRouteTailRecordTokensComputableInPolyTime decider)
    HorizontalRoutedRouteTailRecord.batchedRecordsComputableInPolyTime

/-- The crossover/carrier compiled prefix is polynomial-time. -/
noncomputable def
    directSourceFinalCrossoverCarrierCompiledRecordsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalCrossoverCarrierCompiledRecords decider) := by
  unfold directSourceFinalCrossoverCarrierCompiledRecords
  exact TM2ListAppend.nativeComputableInPolyTime
    (directSourceFinalCrossoverBatchedRecordsComputableInPolyTime decider)
    (directSourceFinalCarrierCompiledBatchedRecordsComputableInPolyTime
      decider)

/-- The bend/routed compiled suffix is polynomial-time. -/
noncomputable def
    directSourceFinalBendRoutedCompiledRecordsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalBendRoutedCompiledRecords decider) := by
  unfold directSourceFinalBendRoutedCompiledRecords
  exact TM2ListAppend.nativeComputableInPolyTime
    (directSourceFinalBendCompiledBatchedRecordsComputableInPolyTime decider)
    (directSourceFinalRoutedBatchedRecordsComputableInPolyTime decider)

/-- The exact five-family final routed-record stream compiles in polynomial
time from direct source symbols. -/
noncomputable def
    directSourceFinalFiveFamilyCompiledRecordsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalFiveFamilyCompiledRecords decider) := by
  unfold directSourceFinalFiveFamilyCompiledRecords
  exact TM2ListAppend.nativeComputableInPolyTime
    (directSourceFinalCrossoverCarrierCompiledRecordsComputableInPolyTime
      decider)
    (directSourceFinalBendRoutedCompiledRecordsComputableInPolyTime decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
