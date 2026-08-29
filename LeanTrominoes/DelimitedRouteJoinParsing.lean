/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedRouteJoinRestoreExecution
import LeanTrominoes.DelimitedRouteJoinScanExecution

/-! # Complete separated-input parsing for delimited-route joining -/

noncomputable section

namespace LeanTrominoes.DelimitedRouteJoin

open StateTransition Turing

def parseTime (prefixes suffixes : List Token) : Nat :=
  4 * prefixes.length + 4 * suffixes.length + 4

def parsing_evalsInTime (prefixes suffixes : List Token) :
    EvalsToInTime machine.step
      (scanLeftCfg
        ⟨prefixes.map .left ++ .separator :: suffixes.map .right,
          [], [], [], [], [], []⟩)
      (some (scanPrefixCfg
        ⟨[], [], prefixes, [], suffixes, [], []⟩))
      (parseTime prefixes suffixes) := by
  let startData : TapeData :=
    ⟨prefixes.map .left ++ .separator :: suffixes.map .right,
      [], [], [], [], [], []⟩
  let afterLeft : TapeData :=
    ⟨suffixes.map .right, prefixes.reverse, [], [], [], [], []⟩
  let afterRight : TapeData :=
    ⟨[], prefixes.reverse, [], suffixes.reverse, [], [], []⟩
  let afterPrefixes : TapeData :=
    ⟨[], [], prefixes, suffixes.reverse, [], [], []⟩
  let parsedData : TapeData :=
    ⟨[], [], prefixes, [], suffixes, [], []⟩
  have leftRun := scanLeft_evalsInTime prefixes
    (suffixes.map .right) startData rfl
  have leftRun' : EvalsToInTime machine.step (scanLeftCfg startData)
      (some (scanRightCfg afterLeft))
      (2 * prefixes.length + 1) := by
    simpa [startData, afterLeft] using leftRun
  have rightRun := scanRight_evalsInTime suffixes afterLeft rfl
  have rightRun' : EvalsToInTime machine.step (scanRightCfg afterLeft)
      (some (restorePrefixesCfg afterRight))
      (2 * suffixes.length + 1) := by
    simpa [afterLeft, afterRight] using rightRun
  have throughRight := EvalsToInTime.trans machine.step
    (2 * prefixes.length + 1) (2 * suffixes.length + 1)
    _ _ _ leftRun' rightRun'
  have prefixesRun := restorePrefixes_evalsInTime
    prefixes.reverse afterRight rfl
  have prefixesRun' : EvalsToInTime machine.step
      (restorePrefixesCfg afterRight)
      (some (restoreSuffixesCfg afterPrefixes))
      (2 * prefixes.length + 1) := by
    simpa [afterRight, afterPrefixes] using prefixesRun
  have throughPrefixes := EvalsToInTime.trans machine.step
    (2 * suffixes.length + 1 + (2 * prefixes.length + 1))
    (2 * prefixes.length + 1) _ _ _ throughRight prefixesRun'
  have suffixesRun := restoreSuffixes_evalsInTime
    suffixes.reverse afterPrefixes rfl
  have suffixesRun' : EvalsToInTime machine.step
      (restoreSuffixesCfg afterPrefixes)
      (some (scanPrefixCfg parsedData))
      (2 * suffixes.length + 1) := by
    simpa [afterPrefixes, parsedData] using suffixesRun
  have whole := EvalsToInTime.trans machine.step
    (2 * prefixes.length + 1 +
      (2 * suffixes.length + 1 + (2 * prefixes.length + 1)))
    (2 * suffixes.length + 1) _ _ _ throughPrefixes suffixesRun'
  convert whole using 1
  simp [parseTime]
  omega

end LeanTrominoes.DelimitedRouteJoin

end
