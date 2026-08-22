/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryAlignedAddRestoreExecution
import LeanTrominoes.UnaryAlignedAddScanParseExecution

/-! # Parsing a separated pair for aligned unary addition -/

noncomputable section

namespace LeanTrominoes
namespace UnaryAlignedAddMachine

open StateTransition Turing

def parseTime (firsts seconds : List UnarySymbol) : Nat :=
  4 * firsts.length + 4 * seconds.length + 4

def parsing_evalsInTime (firsts seconds : List UnarySymbol) :
    EvalsToInTime machine.step
      (scanLeftCfg
        ⟨firsts.map .left ++ .separator :: seconds.map .right,
          [], [], [], [], [], []⟩)
      (some (scanFirstFieldCfg
        ⟨[], [], firsts, [], seconds, [], []⟩))
      (parseTime firsts seconds) := by
  let startData : TapeData :=
    ⟨firsts.map .left ++ .separator :: seconds.map .right,
      [], [], [], [], [], []⟩
  let afterLeft : TapeData :=
    ⟨seconds.map .right, firsts.reverse, [], [], [], [], []⟩
  let afterRight : TapeData :=
    ⟨[], firsts.reverse, [], seconds.reverse, [], [], []⟩
  let afterFirsts : TapeData :=
    ⟨[], [], firsts, seconds.reverse, [], [], []⟩
  let parsedData : TapeData :=
    ⟨[], [], firsts, [], seconds, [], []⟩
  have leftRun := scanLeft_evalsInTime firsts
    (seconds.map .right) startData rfl
  have leftRun' : EvalsToInTime machine.step (scanLeftCfg startData)
      (some (scanRightCfg afterLeft)) (2 * firsts.length + 1) := by
    simpa [startData, afterLeft] using leftRun
  have rightRun := scanRight_evalsInTime seconds afterLeft rfl
  have rightRun' : EvalsToInTime machine.step (scanRightCfg afterLeft)
      (some (restoreFirstsCfg afterRight)) (2 * seconds.length + 1) := by
    simpa [afterLeft, afterRight] using rightRun
  have throughRight := EvalsToInTime.trans machine.step
    (2 * firsts.length + 1) (2 * seconds.length + 1)
    _ _ _ leftRun' rightRun'
  have firstsRun := restoreFirsts_evalsInTime
    firsts.reverse afterRight rfl
  have firstsRun' : EvalsToInTime machine.step
      (restoreFirstsCfg afterRight)
      (some (restoreSecondsCfg afterFirsts))
      (2 * firsts.length + 1) := by
    simpa [afterRight, afterFirsts] using firstsRun
  have throughFirsts := EvalsToInTime.trans machine.step
    (2 * seconds.length + 1 + (2 * firsts.length + 1))
    (2 * firsts.length + 1) _ _ _ throughRight firstsRun'
  have secondsRun := restoreSeconds_evalsInTime
    seconds.reverse afterFirsts rfl
  have secondsRun' : EvalsToInTime machine.step
      (restoreSecondsCfg afterFirsts)
      (some (scanFirstFieldCfg parsedData))
      (2 * seconds.length + 1) := by
    simpa [afterFirsts, parsedData] using secondsRun
  have whole := EvalsToInTime.trans machine.step
    (2 * firsts.length + 1 +
      (2 * seconds.length + 1 + (2 * firsts.length + 1)))
    (2 * seconds.length + 1) _ _ _ throughFirsts secondsRun'
  convert whole using 1
  simp [parseTime]
  omega

end UnaryAlignedAddMachine
end LeanTrominoes
