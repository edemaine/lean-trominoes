/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryBlockRightRotationRestoreExecution
import LeanTrominoes.UnaryBlockRightRotationScanParseExecution

/-! # Parsing a separated pair for unary block right rotation -/

noncomputable section

namespace LeanTrominoes.UnaryBlockRightRotationMachine

open StateTransition Turing

def parseTime (sizes starts : List UnarySymbol) : Nat :=
  4 * sizes.length + 4 * starts.length + 4

def parsing_evalsInTime (sizes starts : List UnarySymbol) :
    EvalsToInTime machine.step
      (scanLeftCfg
        ⟨sizes.map .left ++ .separator :: starts.map .right,
          [], [], [], [], [], [], [], [], [], [], [], []⟩)
      (some (scanSizeFieldCfg
        ⟨[], [], sizes, [], starts, [], [], [], [], [], [], [], []⟩))
      (parseTime sizes starts) := by
  let startData : TapeData :=
    ⟨sizes.map .left ++ .separator :: starts.map .right,
      [], [], [], [], [], [], [], [], [], [], [], []⟩
  let afterLeft : TapeData :=
    ⟨starts.map .right, sizes.reverse, [], [], [], [], [], [], [], [], [], [], []⟩
  let afterRight : TapeData :=
    ⟨[], sizes.reverse, [], starts.reverse, [], [], [], [], [], [], [], [], []⟩
  let afterSizes : TapeData :=
    ⟨[], [], sizes, starts.reverse, [], [], [], [], [], [], [], [], []⟩
  let parsedData : TapeData :=
    ⟨[], [], sizes, [], starts, [], [], [], [], [], [], [], []⟩
  have leftRun := scanLeft_evalsInTime sizes
    (starts.map .right) startData rfl
  have leftRun' : EvalsToInTime machine.step (scanLeftCfg startData)
      (some (scanRightCfg afterLeft)) (2 * sizes.length + 1) := by
    simpa [startData, afterLeft] using leftRun
  have rightRun := scanRight_evalsInTime starts afterLeft rfl
  have rightRun' : EvalsToInTime machine.step (scanRightCfg afterLeft)
      (some (restoreSizesCfg afterRight)) (2 * starts.length + 1) := by
    simpa [afterLeft, afterRight] using rightRun
  have throughRight := EvalsToInTime.trans machine.step
    (2 * sizes.length + 1) (2 * starts.length + 1)
    _ _ _ leftRun' rightRun'
  have sizesRun := restoreSizes_evalsInTime
    sizes.reverse afterRight rfl
  have sizesRun' : EvalsToInTime machine.step
      (restoreSizesCfg afterRight)
      (some (restoreStartsCfg afterSizes))
      (2 * sizes.length + 1) := by
    simpa [afterRight, afterSizes] using sizesRun
  have throughSizes := EvalsToInTime.trans machine.step
    (2 * starts.length + 1 + (2 * sizes.length + 1))
    (2 * sizes.length + 1) _ _ _ throughRight sizesRun'
  have startsRun := restoreStarts_evalsInTime
    starts.reverse afterSizes rfl
  have startsRun' : EvalsToInTime machine.step
      (restoreStartsCfg afterSizes)
      (some (scanSizeFieldCfg parsedData))
      (2 * starts.length + 1) := by
    simpa [afterSizes, parsedData] using startsRun
  have whole := EvalsToInTime.trans machine.step
    (2 * sizes.length + 1 +
      (2 * starts.length + 1 + (2 * sizes.length + 1)))
    (2 * starts.length + 1) _ _ _ throughSizes startsRun'
  convert whole using 1
  simp [parseTime]
  omega

end LeanTrominoes.UnaryBlockRightRotationMachine

end
