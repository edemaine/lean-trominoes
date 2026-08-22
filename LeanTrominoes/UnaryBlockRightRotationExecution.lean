/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryBlockRightRotationReverseExecution
import LeanTrominoes.UnaryBlockRightRotationScanExecution

/-! # Complete execution of unary block right rotation -/

noncomputable section

namespace LeanTrominoes.UnaryBlockRightRotationMachine

open StateTransition Turing

def totalTime (input : Input) : Nat :=
  2 * (outputEncoding input).length + 1 + scanTime input

def execution (input : Input) :
    EvalsToInTime machine.step
      (scanLeftCfg
        ⟨encode input, [], [], [], [], [], [], [], [], [], [], [], []⟩)
      (some (haltCfg (outputEncoding input)))
      (totalTime input) := by
  let scannedData : TapeData :=
    ⟨[], [], [], [], [], [], [], [], [], [], [],
      (outputEncoding input).reverse, []⟩
  have scanRun := scan_evalsInTime input
  have scanRun' : EvalsToInTime machine.step
      (scanLeftCfg
        ⟨encode input, [], [], [], [], [], [], [], [], [], [], [], []⟩)
      (some (reverseOutputCfg scannedData)) (scanTime input) := by
    simpa [scannedData] using scanRun
  have reverseRun := reverseOutput_evalsInTime
    (outputEncoding input).reverse scannedData rfl
  have reverseRun' : EvalsToInTime machine.step
      (reverseOutputCfg scannedData)
      (some (haltCfg (outputEncoding input)))
      (2 * (outputEncoding input).length + 1) := by
    simpa [scannedData, haltCfg, haltDataCfg] using reverseRun
  have whole := EvalsToInTime.trans machine.step
    (scanTime input) (2 * (outputEncoding input).length + 1)
    _ _ _ scanRun' reverseRun'
  simpa [totalTime] using whole

end LeanTrominoes.UnaryBlockRightRotationMachine

end
