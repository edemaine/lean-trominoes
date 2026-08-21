/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsTapeUpdates

/-! # Row-output steps of the Boolean square-row machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace BoolSquareRowsMachine

theorem step_startRows_nil (data : TapeData)
    (sourceEq : data.source = []) :
    TM2.step program (startRowsCfg data) =
      some (clearRowCountdownCfg { data with source := [] }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change source = [] at sourceEq
  subst source
  simp [TM2.step, program, startRowsCfg, clearRowCountdownCfg, cfg,
    tapes, setBit, bitIsNone, clearBit, initialState]

theorem step_startRows_cons (data : TapeData) (bit : Bool)
    (tail : List Bool) (sourceEq : data.source = bit :: tail) :
    TM2.step program (startRowsCfg data) =
      some (emitBitCfg
        { data with
          source := bit :: tail
          outputReverse := .wordStart :: data.outputReverse }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change source = bit :: tail at sourceEq
  subst source
  simp [TM2.step, program, startRowsCfg, emitBitCfg, cfg, tapes,
    setBit, bitIsNone, clearBit, initialState]

theorem step_emitBit_nil (data : TapeData)
    (sourceEq : data.source = []) :
    TM2.step program (emitBitCfg data) =
      some (clearRowCountdownCfg
        { data with
          source := []
          outputReverse := .wordEnd :: data.outputReverse }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change source = [] at sourceEq
  subst source
  simp [TM2.step, program, emitBitCfg, clearRowCountdownCfg, cfg,
    tapes, setBit, bitIsNone, clearBit, initialState]

theorem step_emitBit_cons (data : TapeData) (bit : Bool)
    (tail : List Bool) (sourceEq : data.source = bit :: tail) :
    TM2.step program (emitBitCfg data) =
      some (consumeRowCountCfg
        { data with
          source := tail
          outputReverse := .bit bit :: data.outputReverse }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change source = bit :: tail at sourceEq
  subst source
  simp [TM2.step, program, emitBitCfg, consumeRowCountCfg, cfg, tapes,
    setBit, bitIsNone, bitFromState, clearBit, initialState]

theorem step_consumeRowCount_nil (data : TapeData)
    (countdownEq : data.rowCountdown = []) :
    TM2.step program (consumeRowCountCfg data) =
      some (clearRowRestoreCfg
        { data with
          rowCountdown := []
          outputReverse := .wordEnd :: data.outputReverse }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change rowCountdown = [] at countdownEq
  subst rowCountdown
  simp [TM2.step, program, consumeRowCountCfg, clearRowRestoreCfg, cfg,
    tapes, setPresent, isPresent, clearPresent, initialState]

theorem step_consumeRowCount_cons (data : TapeData)
    (tail : List Unit) (countdownEq : data.rowCountdown = () :: tail) :
    TM2.step program (consumeRowCountCfg data) =
      some (checkRowCountCfg
        { data with
          rowCountdown := tail
          rowRestore := () :: data.rowRestore }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change rowCountdown = () :: tail at countdownEq
  subst rowCountdown
  simp [TM2.step, program, consumeRowCountCfg, checkRowCountCfg, cfg,
    tapes, setPresent, isPresent, clearPresent, initialState]

theorem step_checkRowCount_nil (data : TapeData)
    (countdownEq : data.rowCountdown = []) :
    TM2.step program (checkRowCountCfg data) =
      some (finishRowCfg
        { data with
          rowCountdown := []
          outputReverse := .wordEnd :: data.outputReverse }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change rowCountdown = [] at countdownEq
  subst rowCountdown
  simp [TM2.step, program, checkRowCountCfg, finishRowCfg, cfg, tapes,
    setPresent, isPresent, clearPresent, initialState]

theorem step_checkRowCount_cons (data : TapeData)
    (tail : List Unit) (countdownEq : data.rowCountdown = () :: tail) :
    TM2.step program (checkRowCountCfg data) =
      some (emitBitCfg { data with rowCountdown := () :: tail }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change rowCountdown = () :: tail at countdownEq
  subst rowCountdown
  simp [TM2.step, program, checkRowCountCfg, emitBitCfg, cfg, tapes,
    setPresent, isPresent, clearPresent, initialState]

theorem step_finishRow_nil (data : TapeData)
    (sourceEq : data.source = []) :
    TM2.step program (finishRowCfg data) =
      some (clearRowRestoreCfg { data with source := [] }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change source = [] at sourceEq
  subst source
  simp [TM2.step, program, finishRowCfg, clearRowRestoreCfg, cfg, tapes,
    setBit, bitIsNone, clearBit, initialState]

theorem step_finishRow_cons (data : TapeData) (bit : Bool)
    (tail : List Bool) (sourceEq : data.source = bit :: tail) :
    TM2.step program (finishRowCfg data) =
      some (restoreRowCountCfg { data with source := bit :: tail }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change source = bit :: tail at sourceEq
  subst source
  simp [TM2.step, program, finishRowCfg, restoreRowCountCfg, cfg, tapes,
    setBit, bitIsNone, clearBit, initialState]

theorem step_restoreRowCount_nil (data : TapeData)
    (restoreEq : data.rowRestore = []) :
    TM2.step program (restoreRowCountCfg data) =
      some (emitBitCfg
        { data with
          rowRestore := []
          outputReverse := .wordStart :: data.outputReverse }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change rowRestore = [] at restoreEq
  subst rowRestore
  simp [TM2.step, program, restoreRowCountCfg, emitBitCfg, cfg, tapes,
    setPresent, isPresent, clearPresent, initialState]

theorem step_restoreRowCount_cons (data : TapeData)
    (tail : List Unit) (restoreEq : data.rowRestore = () :: tail) :
    TM2.step program (restoreRowCountCfg data) =
      some (restoreRowCountCfg
        { data with
          rowCountdown := () :: data.rowCountdown
          rowRestore := tail }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change rowRestore = () :: tail at restoreEq
  subst rowRestore
  simp [TM2.step, program, restoreRowCountCfg, cfg, tapes,
    setPresent, isPresent, clearPresent, initialState]

theorem step_clearRowCountdown_nil (data : TapeData)
    (countdownEq : data.rowCountdown = []) :
    TM2.step program (clearRowCountdownCfg data) =
      some (clearRowRestoreCfg { data with rowCountdown := [] }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change rowCountdown = [] at countdownEq
  subst rowCountdown
  simp [TM2.step, program, clearRowCountdownCfg, clearRowRestoreCfg, cfg,
    tapes, setPresent, isPresent, clearPresent, initialState]

theorem step_clearRowCountdown_cons (data : TapeData)
    (tail : List Unit) (countdownEq : data.rowCountdown = () :: tail) :
    TM2.step program (clearRowCountdownCfg data) =
      some (clearRowCountdownCfg { data with rowCountdown := tail }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change rowCountdown = () :: tail at countdownEq
  subst rowCountdown
  simp [TM2.step, program, clearRowCountdownCfg, cfg, tapes,
    setPresent, isPresent, clearPresent, initialState]

theorem step_clearRowRestore_nil (data : TapeData)
    (restoreEq : data.rowRestore = []) :
    TM2.step program (clearRowRestoreCfg data) =
      some (reverseOutputCfg { data with rowRestore := [] }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change rowRestore = [] at restoreEq
  subst rowRestore
  simp [TM2.step, program, clearRowRestoreCfg, reverseOutputCfg, cfg,
    tapes, setPresent, isPresent, clearPresent, initialState]

theorem step_clearRowRestore_cons (data : TapeData)
    (tail : List Unit) (restoreEq : data.rowRestore = () :: tail) :
    TM2.step program (clearRowRestoreCfg data) =
      some (clearRowRestoreCfg { data with rowRestore := tail }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change rowRestore = () :: tail at restoreEq
  subst rowRestore
  simp [TM2.step, program, clearRowRestoreCfg, cfg, tapes,
    setPresent, isPresent, clearPresent, initialState]

theorem step_reverseOutput_nil (output : List OutputToken) :
    TM2.step program
        (reverseOutputCfg
          ⟨[], [], [], [], [], [], [], [], [], [], output⟩) =
      some (haltCfg output) := by
  simp [TM2.step, program, reverseOutputCfg, haltCfg, cfg, tapes,
    setOutputToken, outputTokenIsNone, initialState]

theorem step_reverseOutput_cons (token : OutputToken)
    (tokens output : List OutputToken) :
    TM2.step program
        (reverseOutputCfg
          ⟨[], [], [], [], [], [], [], [], [], token :: tokens, output⟩) =
      some (reverseOutputCfg
        ⟨[], [], [], [], [], [], [], [], [], tokens, token :: output⟩) := by
  simp [TM2.step, program, reverseOutputCfg, cfg, tapes,
    setOutputToken, outputTokenIsNone, outputTokenFromState,
    clearOutputToken, initialState]

end BoolSquareRowsMachine
end LeanTrominoes
