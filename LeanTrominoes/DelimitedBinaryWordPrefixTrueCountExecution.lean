/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountCleanupExecution
import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountListExecution

/-! # Complete execution of row-prefix true counts -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPrefixTrueCountMachine

def outputWord (rows : List (List Bool)) : List OutputSymbol :=
  UnaryFieldEncoderMachine.unaryFields
    (DelimitedBinaryWordPrefixTrueCounts.countsAux 0 rows)

def totalTime (rows : List (List Bool)) : Nat :=
  (outputWord rows).length + 1 +
    (rows.length + 1 + (1 + rowsTime 0 rows))

def execution (rows : List (List Bool)) :
    EvalsToInTime (TM2.step program)
      (scanStartCfg
        ⟨DelimitedBinaryWords.encode ⟨rows⟩, [], [], [], [], []⟩)
      (some (haltCfg (outputWord rows)))
      (totalTime rows) := by
  let startData : TapeData :=
    ⟨DelimitedBinaryWords.encode ⟨rows⟩, [], [], [], [], []⟩
  let scannedData : TapeData :=
    ⟨[], List.replicate rows.length (), [], [],
      (outputWord rows).reverse, []⟩
  let clearedData : TapeData :=
    ⟨[], [], [], [], (outputWord rows).reverse, []⟩
  have rowsRun := rows_evalsInTime 0 rows [] startData
    (by simp [startData]) (by simp [startData])
    (by simp [startData]) (by simp [startData])
  have rowsRun' :
      EvalsToInTime (TM2.step program) (scanStartCfg startData)
        (some (scanStartCfg scannedData)) (rowsTime 0 rows) := by
    simpa [startData, scannedData, outputWord] using rowsRun
  have finishScan := FiniteBlockTransducer.oneStep
    (step_scanStart_nil scannedData rfl)
  have throughScan := EvalsToInTime.trans (TM2.step program)
    (rowsTime 0 rows) 1
    (scanStartCfg startData) (scanStartCfg scannedData)
    (some (clearRowIndexCfg scannedData)) rowsRun' finishScan
  have clearRun := clearRowIndex_evalsInTime
    (List.replicate rows.length ()) scannedData rfl
  have clearRun' :
      EvalsToInTime (TM2.step program) (clearRowIndexCfg scannedData)
        (some (reverseOutputCfg clearedData)) (rows.length + 1) := by
    simpa [clearedData, scannedData] using clearRun
  have throughClear := EvalsToInTime.trans (TM2.step program)
    (1 + rowsTime 0 rows) (rows.length + 1)
    (scanStartCfg startData) (clearRowIndexCfg scannedData)
    (some (reverseOutputCfg clearedData)) throughScan clearRun'
  have reverseRun := reverseOutput_evalsInTime
    (outputWord rows).reverse clearedData rfl
  have reverseRun' :
      EvalsToInTime (TM2.step program) (reverseOutputCfg clearedData)
        (some (haltCfg (outputWord rows)))
        ((outputWord rows).length + 1) := by
    simpa [clearedData, haltCfg, haltDataCfg] using reverseRun
  have composed := EvalsToInTime.trans (TM2.step program)
    (rows.length + 1 + (1 + rowsTime 0 rows))
    ((outputWord rows).length + 1)
    (scanStartCfg startData) (reverseOutputCfg clearedData)
    (some (haltCfg (outputWord rows))) throughClear reverseRun'
  simpa [startData, totalTime] using composed

end DelimitedBinaryWordPrefixTrueCountMachine
end LeanTrominoes
