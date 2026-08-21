/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnarySuccessorEqualityFilterParseExecution

/-! # Parsing a complete separated pair of unary streams -/

noncomputable section

namespace LeanTrominoes
namespace UnarySuccessorEqualityFilterMachine

open StateTransition Turing

/-- Exact cost of copying both separated streams onto their working tapes. -/
def parseTime (ranks sizes : List UnarySymbol) : Nat :=
  4 * ranks.length + 4 * sizes.length + 4

/-- Parse a canonical separated pair into forward rank and size work tapes. -/
def parsing_evalsInTime (ranks sizes : List UnarySymbol) :
    EvalsToInTime machine.step
      (scanLeftCfg
        ⟨ranks.map .left ++ .separator :: sizes.map .right,
          [], [], [], [], [], [], []⟩)
      (some (scanRankCfg
        ⟨[], [], ranks, [], sizes, [], [], []⟩))
      (parseTime ranks sizes) := by
  let startData : TapeData :=
    ⟨ranks.map .left ++ .separator :: sizes.map .right,
      [], [], [], [], [], [], []⟩
  let afterLeft : TapeData :=
    ⟨sizes.map .right, ranks.reverse, [], [], [], [], [], []⟩
  let afterRight : TapeData :=
    ⟨[], ranks.reverse, [], sizes.reverse, [], [], [], []⟩
  let afterRanks : TapeData :=
    ⟨[], [], ranks, sizes.reverse, [], [], [], []⟩
  let parsedData : TapeData :=
    ⟨[], [], ranks, [], sizes, [], [], []⟩
  have leftRun := scanLeft_evalsInTime ranks
    (sizes.map .right) startData rfl
  have leftRun' : EvalsToInTime machine.step (scanLeftCfg startData)
      (some (scanRightCfg afterLeft)) (2 * ranks.length + 1) := by
    simpa [startData, afterLeft] using leftRun
  have rightRun := scanRight_evalsInTime sizes afterLeft rfl
  have rightRun' : EvalsToInTime machine.step (scanRightCfg afterLeft)
      (some (restoreRanksCfg afterRight)) (2 * sizes.length + 1) := by
    simpa [afterLeft, afterRight] using rightRun
  have throughRight := EvalsToInTime.trans machine.step
    (2 * ranks.length + 1) (2 * sizes.length + 1)
    _ _ _ leftRun' rightRun'
  have ranksRun := restoreRanks_evalsInTime ranks.reverse afterRight rfl
  have ranksRun' : EvalsToInTime machine.step (restoreRanksCfg afterRight)
      (some (restoreSizesCfg afterRanks)) (2 * ranks.length + 1) := by
    simpa [afterRight, afterRanks] using ranksRun
  have throughRanks := EvalsToInTime.trans machine.step
    (2 * sizes.length + 1 + (2 * ranks.length + 1))
    (2 * ranks.length + 1) _ _ _ throughRight ranksRun'
  have sizesRun := restoreSizes_evalsInTime sizes.reverse afterRanks rfl
  have sizesRun' : EvalsToInTime machine.step (restoreSizesCfg afterRanks)
      (some (scanRankCfg parsedData)) (2 * sizes.length + 1) := by
    simpa [afterRanks, parsedData] using sizesRun
  have whole := EvalsToInTime.trans machine.step
    (2 * ranks.length + 1 + (2 * sizes.length + 1 +
      (2 * ranks.length + 1)))
    (2 * sizes.length + 1) _ _ _ throughRanks sizesRun'
  convert whole using 1
  simp [parseTime]
  omega

end UnarySuccessorEqualityFilterMachine
end LeanTrominoes
