/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupParseExecution

/-! # Parsing a separated row/value stream for last-true lookup -/

noncomputable section

namespace LeanTrominoes
namespace LastTrueUnaryValueLookupMachine

open StateTransition Turing

/-- Exact cost of copying both separated streams onto their working tapes. -/
def parseTime (rows : List RowSymbol) (values : List UnarySymbol) : Nat :=
  4 * rows.length + 4 * values.length + 4

def parsing_evalsInTime (rows : List RowSymbol)
    (values : List UnarySymbol) :
    EvalsToInTime machine.step
      (scanLeftCfg
        ⟨rows.map .left ++ .separator :: values.map .right,
          [], [], [], [], [], [], [], []⟩)
      (some (scanRowsCfg
        ⟨[], [], rows, [], values, [], [], [], []⟩))
      (parseTime rows values) := by
  let startData : TapeData :=
    ⟨rows.map .left ++ .separator :: values.map .right,
      [], [], [], [], [], [], [], []⟩
  let afterLeft : TapeData :=
    ⟨values.map .right, rows.reverse, [], [], [], [], [], [], []⟩
  let afterRight : TapeData :=
    ⟨[], rows.reverse, [], values.reverse, [], [], [], [], []⟩
  let afterRows : TapeData :=
    ⟨[], [], rows, values.reverse, [], [], [], [], []⟩
  let parsedData : TapeData :=
    ⟨[], [], rows, [], values, [], [], [], []⟩
  have leftRun := scanLeft_evalsInTime rows
    (values.map .right) startData rfl
  have leftRun' : EvalsToInTime machine.step (scanLeftCfg startData)
      (some (scanRightCfg afterLeft)) (2 * rows.length + 1) := by
    simpa [startData, afterLeft] using leftRun
  have rightRun := scanRight_evalsInTime values afterLeft rfl
  have rightRun' : EvalsToInTime machine.step (scanRightCfg afterLeft)
      (some (restoreRowsCfg afterRight)) (2 * values.length + 1) := by
    simpa [afterLeft, afterRight] using rightRun
  have throughRight := EvalsToInTime.trans machine.step
    (2 * rows.length + 1) (2 * values.length + 1)
    _ _ _ leftRun' rightRun'
  have rowsRun := restoreRows_evalsInTime rows.reverse afterRight rfl
  have rowsRun' : EvalsToInTime machine.step (restoreRowsCfg afterRight)
      (some (restoreInitialValuesCfg afterRows))
      (2 * rows.length + 1) := by
    simpa [afterRight, afterRows] using rowsRun
  have throughRows := EvalsToInTime.trans machine.step
    (2 * values.length + 1 + (2 * rows.length + 1))
    (2 * rows.length + 1) _ _ _ throughRight rowsRun'
  have valuesRun := restoreInitialValues_evalsInTime
    values.reverse afterRows rfl
  have valuesRun' : EvalsToInTime machine.step
      (restoreInitialValuesCfg afterRows)
      (some (scanRowsCfg parsedData)) (2 * values.length + 1) := by
    simpa [afterRows, parsedData] using valuesRun
  have whole := EvalsToInTime.trans machine.step
    (2 * rows.length + 1 +
      (2 * values.length + 1 + (2 * rows.length + 1)))
    (2 * values.length + 1) _ _ _ throughRows valuesRun'
  convert whole using 1
  simp [parseTime]
  omega

end LastTrueUnaryValueLookupMachine
end LeanTrominoes
