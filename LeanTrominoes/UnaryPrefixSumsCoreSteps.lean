/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.UnaryPrefixSumsTapeUpdates

/-! # Core one-step transitions of the unary prefix-sum machine -/

namespace LeanTrominoes

open StateTransition Turing

namespace UnaryPrefixSumsMachine

theorem step_readField_nil (data : TapeData) (inputEq : data.input = []) :
    TM2.step program (readFieldCfg data) =
      some (clearSumCfg { data with input := [] }) := by
  rcases data with ⟨input, sum, sumRestore, outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, readFieldCfg, clearSumCfg, cfg, tapes,
    setSaved, savedIsNone]

theorem step_readField_cons (data : TapeData) (symbol : Symbol)
    (tail : List Symbol) (inputEq : data.input = symbol :: tail) :
    TM2.step program (readFieldCfg data) =
      some (copySumCfg symbol { data with input := tail }) := by
  rcases data with ⟨input, sum, sumRestore, outputReverse, output⟩
  change input = symbol :: tail at inputEq
  subst input
  simp [TM2.step, program, readFieldCfg, copySumCfg, cfg, tapes,
    setSaved, savedIsNone]

theorem step_copySum_nil (saved : Symbol) (data : TapeData)
    (sumEq : data.sum = []) :
    TM2.step program (copySumCfg saved data) =
      some (restoreSumCfg saved
        { data with
          sum := []
          outputReverse := .delimiter :: data.outputReverse }) := by
  rcases data with ⟨input, sum, sumRestore, outputReverse, output⟩
  change sum = [] at sumEq
  subst sum
  simp [TM2.step, program, copySumCfg, restoreSumCfg, cfg, tapes,
    setPresence, poppedIsNone]

theorem step_copySum_cons (saved symbol : Symbol) (tail : List Symbol)
    (data : TapeData) (sumEq : data.sum = symbol :: tail) :
    TM2.step program (copySumCfg saved data) =
      some (copySumCfg saved
        { data with
          sum := tail
          sumRestore := .unit :: data.sumRestore
          outputReverse := .unit :: data.outputReverse }) := by
  rcases data with ⟨input, sum, sumRestore, outputReverse, output⟩
  change sum = symbol :: tail at sumEq
  subst sum
  simp [TM2.step, program, copySumCfg, cfg, tapes, setPresence,
    poppedIsNone, clearPresence]

theorem step_restoreSum_nil (saved : Symbol) (data : TapeData)
    (restoreEq : data.sumRestore = []) :
    TM2.step program (restoreSumCfg saved data) =
      some (consumeSavedCfg saved { data with sumRestore := [] }) := by
  rcases data with ⟨input, sum, sumRestore, outputReverse, output⟩
  change sumRestore = [] at restoreEq
  subst sumRestore
  simp [TM2.step, program, restoreSumCfg, consumeSavedCfg, cfg, tapes,
    setPresence, poppedIsNone]

theorem step_restoreSum_cons (saved symbol : Symbol) (tail : List Symbol)
    (data : TapeData) (restoreEq : data.sumRestore = symbol :: tail) :
    TM2.step program (restoreSumCfg saved data) =
      some (restoreSumCfg saved
        { data with
          sum := .unit :: data.sum
          sumRestore := tail }) := by
  rcases data with ⟨input, sum, sumRestore, outputReverse, output⟩
  change sumRestore = symbol :: tail at restoreEq
  subst sumRestore
  simp [TM2.step, program, restoreSumCfg, cfg, tapes, setPresence,
    poppedIsNone, clearPresence]

theorem step_consumeSaved_unit (data : TapeData) :
    TM2.step program (consumeSavedCfg .unit data) =
      some (scanFieldCfg { data with sum := .unit :: data.sum }) := by
  rcases data with ⟨input, sum, sumRestore, outputReverse, output⟩
  simp [TM2.step, program, consumeSavedCfg, scanFieldCfg, cfg, tapes,
    savedIsUnit, clearState]

theorem step_consumeSaved_delimiter (data : TapeData) :
    TM2.step program (consumeSavedCfg .delimiter data) =
      some (readFieldCfg data) := by
  rcases data with ⟨input, sum, sumRestore, outputReverse, output⟩
  simp [TM2.step, program, consumeSavedCfg, readFieldCfg, cfg, tapes,
    savedIsUnit, clearState]

end UnaryPrefixSumsMachine
end LeanTrominoes
