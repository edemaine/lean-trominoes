/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsTapeUpdates

/-! # Counting and setup steps of the Boolean square-row machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace BoolSquareRowsMachine

theorem step_copyInput_nil (data : TapeData)
    (inputEq : data.input = []) :
    TM2.step program (copyInputCfg data) =
      some (initOddCfg { data with input := [] }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, copyInputCfg, initOddCfg, cfg, tapes,
    setBit, bitIsNone, clearBit, initialState]

theorem step_copyInput_cons (data : TapeData) (bit : Bool)
    (tail : List Bool) (inputEq : data.input = bit :: tail) :
    TM2.step program (copyInputCfg data) =
      some (copyInputCfg
        { data with
          input := tail
          sourceReverse := bit :: data.sourceReverse
          work := () :: data.work }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change input = bit :: tail at inputEq
  subst input
  simp [TM2.step, program, copyInputCfg, cfg, tapes, setBit,
    bitIsNone, bitFromState, clearBit, initialState]

theorem step_initOdd (data : TapeData) :
    TM2.step program (initOddCfg data) =
      some (consumeWorkCfg { data with odd := () :: data.odd }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  simp [TM2.step, program, initOddCfg, consumeWorkCfg, cfg, tapes,
    initialState]

theorem step_consumeWork_nil (data : TapeData)
    (workEq : data.work = []) :
    TM2.step program (consumeWorkCfg data) =
      some (clearOddCfg { data with work := [] }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change work = [] at workEq
  subst work
  simp [TM2.step, program, consumeWorkCfg, clearOddCfg, cfg, tapes,
    setPresent, isPresent, clearPresent, initialState]

theorem step_consumeWork_cons (data : TapeData) (tail : List Unit)
    (workEq : data.work = () :: tail) :
    TM2.step program (consumeWorkCfg data) =
      some (consumeOddCfg { data with work := tail }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change work = () :: tail at workEq
  subst work
  simp [TM2.step, program, consumeWorkCfg, consumeOddCfg, cfg, tapes,
    setPresent, isPresent, clearPresent, initialState]

theorem step_consumeOdd_nil (data : TapeData)
    (oddEq : data.odd = []) :
    TM2.step program (consumeOddCfg data) =
      some (clearOddCfg { data with odd := [] }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change odd = [] at oddEq
  subst odd
  simp [TM2.step, program, consumeOddCfg, clearOddCfg, cfg, tapes,
    setPresent, isPresent, clearPresent, initialState]

theorem step_consumeOdd_cons (data : TapeData) (tail : List Unit)
    (oddEq : data.odd = () :: tail) :
    TM2.step program (consumeOddCfg data) =
      some (checkOddCfg
        { data with
          odd := tail
          oddRestore := () :: data.oddRestore }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change odd = () :: tail at oddEq
  subst odd
  simp [TM2.step, program, consumeOddCfg, checkOddCfg, cfg, tapes,
    setPresent, isPresent, clearPresent, initialState]

theorem step_checkOdd_nil (data : TapeData) (oddEq : data.odd = []) :
    TM2.step program (checkOddCfg data) =
      some (finishRootStepCfg { data with odd := [] }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change odd = [] at oddEq
  subst odd
  simp [TM2.step, program, checkOddCfg, finishRootStepCfg, cfg, tapes,
    setPresent, isPresent, clearPresent, initialState]

theorem step_checkOdd_cons (data : TapeData) (tail : List Unit)
    (oddEq : data.odd = () :: tail) :
    TM2.step program (checkOddCfg data) =
      some (consumeWorkCfg { data with odd := () :: tail }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change odd = () :: tail at oddEq
  subst odd
  simp [TM2.step, program, checkOddCfg, consumeWorkCfg, cfg, tapes,
    setPresent, isPresent, clearPresent, initialState]

theorem step_finishRootStep_nil (data : TapeData)
    (workEq : data.work = []) :
    TM2.step program (finishRootStepCfg data) =
      some (clearOddCfg
        { data with
          work := []
          root := () :: data.root }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change work = [] at workEq
  subst work
  simp [TM2.step, program, finishRootStepCfg, clearOddCfg, cfg, tapes,
    setPresent, isPresent, clearPresent, initialState]

theorem step_finishRootStep_cons (data : TapeData) (tail : List Unit)
    (workEq : data.work = () :: tail) :
    TM2.step program (finishRootStepCfg data) =
      some (restoreOddCfg
        { data with
          work := () :: tail
          root := () :: data.root }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change work = () :: tail at workEq
  subst work
  simp [TM2.step, program, finishRootStepCfg, restoreOddCfg, cfg, tapes,
    setPresent, isPresent, clearPresent, initialState]

theorem step_restoreOdd_nil (data : TapeData)
    (restoreEq : data.oddRestore = []) :
    TM2.step program (restoreOddCfg data) =
      some (consumeWorkCfg
        { data with
          odd := () :: () :: data.odd
          oddRestore := [] }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change oddRestore = [] at restoreEq
  subst oddRestore
  simp [TM2.step, program, restoreOddCfg, consumeWorkCfg, cfg, tapes,
    setPresent, isPresent, clearPresent, initialState]

theorem step_restoreOdd_cons (data : TapeData) (tail : List Unit)
    (restoreEq : data.oddRestore = () :: tail) :
    TM2.step program (restoreOddCfg data) =
      some (restoreOddCfg
        { data with
          odd := () :: data.odd
          oddRestore := tail }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change oddRestore = () :: tail at restoreEq
  subst oddRestore
  simp [TM2.step, program, restoreOddCfg, cfg, tapes,
    setPresent, isPresent, clearPresent, initialState]

theorem step_clearOdd_nil (data : TapeData) (oddEq : data.odd = []) :
    TM2.step program (clearOddCfg data) =
      some (clearOddRestoreCfg { data with odd := [] }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change odd = [] at oddEq
  subst odd
  simp [TM2.step, program, clearOddCfg, clearOddRestoreCfg, cfg, tapes,
    setPresent, isPresent, clearPresent, initialState]

theorem step_clearOdd_cons (data : TapeData) (tail : List Unit)
    (oddEq : data.odd = () :: tail) :
    TM2.step program (clearOddCfg data) =
      some (clearOddCfg { data with odd := tail }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change odd = () :: tail at oddEq
  subst odd
  simp [TM2.step, program, clearOddCfg, cfg, tapes,
    setPresent, isPresent, clearPresent, initialState]

theorem step_clearOddRestore_nil (data : TapeData)
    (restoreEq : data.oddRestore = []) :
    TM2.step program (clearOddRestoreCfg data) =
      some (moveRootCfg { data with oddRestore := [] }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change oddRestore = [] at restoreEq
  subst oddRestore
  simp [TM2.step, program, clearOddRestoreCfg, moveRootCfg, cfg, tapes,
    setPresent, isPresent, clearPresent, initialState]

theorem step_clearOddRestore_cons (data : TapeData) (tail : List Unit)
    (restoreEq : data.oddRestore = () :: tail) :
    TM2.step program (clearOddRestoreCfg data) =
      some (clearOddRestoreCfg { data with oddRestore := tail }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change oddRestore = () :: tail at restoreEq
  subst oddRestore
  simp [TM2.step, program, clearOddRestoreCfg, cfg, tapes,
    setPresent, isPresent, clearPresent, initialState]

theorem step_moveRoot_nil (data : TapeData) (rootEq : data.root = []) :
    TM2.step program (moveRootCfg data) =
      some (reverseSourceCfg { data with root := [] }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change root = [] at rootEq
  subst root
  simp [TM2.step, program, moveRootCfg, reverseSourceCfg, cfg, tapes,
    setPresent, isPresent, clearPresent, initialState]

theorem step_moveRoot_cons (data : TapeData) (tail : List Unit)
    (rootEq : data.root = () :: tail) :
    TM2.step program (moveRootCfg data) =
      some (moveRootCfg
        { data with
          root := tail
          rowCountdown := () :: data.rowCountdown }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change root = () :: tail at rootEq
  subst root
  simp [TM2.step, program, moveRootCfg, cfg, tapes,
    setPresent, isPresent, clearPresent, initialState]

theorem step_reverseSource_nil (data : TapeData)
    (reverseEq : data.sourceReverse = []) :
    TM2.step program (reverseSourceCfg data) =
      some (startRowsCfg { data with sourceReverse := [] }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change sourceReverse = [] at reverseEq
  subst sourceReverse
  simp [TM2.step, program, reverseSourceCfg, startRowsCfg, cfg, tapes,
    setBit, bitIsNone, clearBit, initialState]

theorem step_reverseSource_cons (data : TapeData) (bit : Bool)
    (tail : List Bool) (reverseEq : data.sourceReverse = bit :: tail) :
    TM2.step program (reverseSourceCfg data) =
      some (reverseSourceCfg
        { data with
          sourceReverse := tail
          source := bit :: data.source }) := by
  rcases data with
    ⟨input, sourceReverse, work, odd, oddRestore, root, source,
      rowCountdown, rowRestore, outputReverse, output⟩
  change sourceReverse = bit :: tail at reverseEq
  subst sourceReverse
  simp [TM2.step, program, reverseSourceCfg, cfg, tapes, setBit,
    bitIsNone, bitFromState, clearBit, initialState]

end BoolSquareRowsMachine
end LeanTrominoes
