/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.UnaryPrefixSumsTapeUpdates

/-! # Scan and reversal steps of the unary prefix-sum machine -/

namespace LeanTrominoes

open StateTransition Turing

namespace UnaryPrefixSumsMachine

theorem step_scanField_nil (data : TapeData) (inputEq : data.input = []) :
    TM2.step program (scanFieldCfg data) =
      some (reverseOutputCfg { data with input := [] }) := by
  rcases data with ⟨input, sum, sumRestore, outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, scanFieldCfg, reverseOutputCfg, cfg, tapes,
    setSaved, savedIsNone]

theorem step_scanField_unit (data : TapeData) (tail : List Symbol)
    (inputEq : data.input = .unit :: tail) :
    TM2.step program (scanFieldCfg data) =
      some (scanFieldCfg
        { data with
          input := tail
          sum := .unit :: data.sum }) := by
  rcases data with ⟨input, sum, sumRestore, outputReverse, output⟩
  change input = UnaryFieldEncoderMachine.Symbol.unit :: tail at inputEq
  subst input
  simp [TM2.step, program, scanFieldCfg, cfg, tapes, setSaved,
    savedIsNone, savedIsUnit, clearState]

theorem step_scanField_delimiter (data : TapeData) (tail : List Symbol)
    (inputEq : data.input = .delimiter :: tail) :
    TM2.step program (scanFieldCfg data) =
      some (readFieldCfg { data with input := tail }) := by
  rcases data with ⟨input, sum, sumRestore, outputReverse, output⟩
  change input = UnaryFieldEncoderMachine.Symbol.delimiter :: tail at inputEq
  subst input
  simp [TM2.step, program, scanFieldCfg, readFieldCfg, cfg, tapes,
    setSaved, savedIsNone, savedIsUnit, clearState]

theorem step_reverseOutput_nil (data : TapeData)
    (reverseEq : data.outputReverse = []) :
    TM2.step program (reverseOutputCfg data) =
      some (haltDataCfg { data with outputReverse := [] }) := by
  rcases data with ⟨input, sum, sumRestore, outputReverse, output⟩
  change outputReverse = [] at reverseEq
  subst outputReverse
  simp [TM2.step, program, reverseOutputCfg, haltDataCfg, cfg, tapes,
    setSaved, savedIsNone]

theorem step_reverseOutput_cons (data : TapeData) (symbol : Symbol)
    (tail : List Symbol)
    (reverseEq : data.outputReverse = symbol :: tail) :
    TM2.step program (reverseOutputCfg data) =
      some (reverseOutputCfg
        { data with
          outputReverse := tail
          output := symbol :: data.output }) := by
  rcases data with ⟨input, sum, sumRestore, outputReverse, output⟩
  change outputReverse = symbol :: tail at reverseEq
  subst outputReverse
  simp [TM2.step, program, reverseOutputCfg, cfg, tapes, setSaved,
    savedIsNone, savedSymbol, clearState]

end UnaryPrefixSumsMachine
end LeanTrominoes
