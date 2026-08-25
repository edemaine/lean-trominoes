/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairExcessMachine

/-! # One-step equations for unary word-pair excesses -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairExcessMachine

open DelimitedBinaryWordPairs

@[simp] theorem update_tapes_input (data : TapeData)
    (value : List Token) :
    Function.update (tapes data) Stack.input value =
      tapes { data with input := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_first (data : TapeData)
    (value : List Bool) :
    Function.update (tapes data) Stack.first value =
      tapes { data with first := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_second (data : TapeData)
    (value : List Bool) :
    Function.update (tapes data) Stack.second value =
      tapes { data with second := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_outputReverse (data : TapeData)
    (value : List UnaryFieldEncoderMachine.Symbol) :
    Function.update (tapes data) Stack.outputReverse value =
      tapes { data with outputReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_output (data : TapeData)
    (value : List UnaryFieldEncoderMachine.Symbol) :
    Function.update (tapes data) Stack.output value =
      tapes { data with output := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem step_scan_nil (keepFirst : Bool) (data : TapeData)
    (inputEq : data.input = []) :
    TM2.step (program keepFirst) (scanCfg data) =
      some (reverseOutputCfg { data with input := [] }) := by
  rcases data with ⟨input, first, second, outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, scanCfg, reverseOutputCfg, cfg, tapes,
    tokenIsNone, setToken, initialState]

theorem step_scan_pairStart (keepFirst : Bool) (data : TapeData)
    (tail : List Token) (inputEq : data.input = .pairStart :: tail) :
    TM2.step (program keepFirst) (scanCfg data) =
      some (readFirstCfg { data with input := tail }) := by
  rcases data with ⟨input, first, second, outputReverse, output⟩
  change input = .pairStart :: tail at inputEq
  subst input
  simp [TM2.step, program, scanCfg, readFirstCfg, cfg, tapes,
    tokenIsNone, setToken, clearToken, initialState]

theorem step_readFirst_bit (keepFirst : Bool) (data : TapeData)
    (bit : Bool) (tail : List Token)
    (inputEq : data.input = .firstBit bit :: tail) :
    TM2.step (program keepFirst) (readFirstCfg data) =
      some (readFirstCfg
        { data with input := tail, first := bit :: data.first }) := by
  rcases data with ⟨input, first, second, outputReverse, output⟩
  change input = .firstBit bit :: tail at inputEq
  subst input
  simp [TM2.step, program, readFirstCfg, cfg, tapes, setToken,
    tokenIsFirstBit, tokenBitFromState, clearToken, initialState]

theorem step_readFirst_middle (keepFirst : Bool) (data : TapeData)
    (tail : List Token) (inputEq : data.input = .middle :: tail) :
    TM2.step (program keepFirst) (readFirstCfg data) =
      some (readSecondCfg { data with input := tail }) := by
  rcases data with ⟨input, first, second, outputReverse, output⟩
  change input = .middle :: tail at inputEq
  subst input
  simp [TM2.step, program, readFirstCfg, readSecondCfg, cfg, tapes,
    setToken, tokenIsFirstBit, clearToken, initialState]

theorem step_readSecond_bit (keepFirst : Bool) (data : TapeData)
    (bit : Bool) (tail : List Token)
    (inputEq : data.input = .secondBit bit :: tail) :
    TM2.step (program keepFirst) (readSecondCfg data) =
      some (readSecondCfg
        { data with input := tail, second := bit :: data.second }) := by
  rcases data with ⟨input, first, second, outputReverse, output⟩
  change input = .secondBit bit :: tail at inputEq
  subst input
  simp [TM2.step, program, readSecondCfg, cfg, tapes, setToken,
    tokenIsSecondBit, tokenBitFromState, clearToken, initialState]

theorem step_readSecond_pairEnd (keepFirst : Bool) (data : TapeData)
    (tail : List Token) (inputEq : data.input = .pairEnd :: tail) :
    TM2.step (program keepFirst) (readSecondCfg data) =
      some (cancelCfg { data with input := tail }) := by
  rcases data with ⟨input, first, second, outputReverse, output⟩
  change input = .pairEnd :: tail at inputEq
  subst input
  simp [TM2.step, program, readSecondCfg, cancelCfg, cfg, tapes,
    setToken, tokenIsSecondBit, clearToken, initialState]

theorem step_cancel_nil_nil (keepFirst : Bool) (data : TapeData)
    (firstEq : data.first = []) (secondEq : data.second = []) :
    TM2.step (program keepFirst) (cancelCfg data) =
      some (emitDelimiterCfg
        { data with first := [], second := [] }) := by
  rcases data with ⟨input, first, second, outputReverse, output⟩
  change first = [] at firstEq
  change second = [] at secondEq
  subst first
  subst second
  simp [TM2.step, program, cancelCfg, emitDelimiterCfg, cfg, tapes,
    setFirst, setSecond, bothPresent, bothAbsent, clearPair, initialState]

theorem step_cancel_cons_cons (keepFirst : Bool) (data : TapeData)
    (firstBit secondBit : Bool) (firstTail secondTail : List Bool)
    (firstEq : data.first = firstBit :: firstTail)
    (secondEq : data.second = secondBit :: secondTail) :
    TM2.step (program keepFirst) (cancelCfg data) =
      some (cancelCfg
        { data with first := firstTail, second := secondTail }) := by
  rcases data with ⟨input, first, second, outputReverse, output⟩
  change first = firstBit :: firstTail at firstEq
  change second = secondBit :: secondTail at secondEq
  subst first
  subst second
  simp [TM2.step, program, cancelCfg, cfg, tapes, setFirst, setSecond,
    bothPresent, clearPair, initialState]

theorem step_cancel_cons_nil (keepFirst : Bool) (data : TapeData)
    (firstBit : Bool) (firstTail : List Bool)
    (firstEq : data.first = firstBit :: firstTail)
    (secondEq : data.second = []) :
    TM2.step (program keepFirst) (cancelCfg data) =
      some (drainFirstCfg keepFirst
        { data with
          first := firstTail
          second := []
          outputReverse :=
            if keepFirst then .unit :: data.outputReverse
            else data.outputReverse }) := by
  rcases data with ⟨input, first, second, outputReverse, output⟩
  change first = firstBit :: firstTail at firstEq
  change second = [] at secondEq
  subst first
  subst second
  cases keepFirst <;>
    simp [TM2.step, program, cancelCfg, drainFirstCfg, cfg, tapes,
      setFirst, setSecond, bothPresent, bothAbsent, firstPresent, clearPair,
      initialState]

theorem step_cancel_nil_cons (keepFirst : Bool) (data : TapeData)
    (secondBit : Bool) (secondTail : List Bool)
    (firstEq : data.first = [])
    (secondEq : data.second = secondBit :: secondTail) :
    TM2.step (program keepFirst) (cancelCfg data) =
      some (drainSecondCfg (!keepFirst)
        { data with
          first := []
          second := secondTail
          outputReverse :=
            if keepFirst then data.outputReverse
            else .unit :: data.outputReverse }) := by
  rcases data with ⟨input, first, second, outputReverse, output⟩
  change first = [] at firstEq
  change second = secondBit :: secondTail at secondEq
  subst first
  subst second
  cases keepFirst <;>
    simp [TM2.step, program, cancelCfg, drainSecondCfg, cfg, tapes,
      setFirst, setSecond, bothPresent, bothAbsent, firstPresent, clearPair,
      initialState]

theorem step_drainFirst_nil (keepFirst emit : Bool) (data : TapeData)
    (firstEq : data.first = []) :
    TM2.step (program keepFirst) (drainFirstCfg emit data) =
      some (emitDelimiterCfg { data with first := [] }) := by
  rcases data with ⟨input, first, second, outputReverse, output⟩
  change first = [] at firstEq
  subst first
  simp [TM2.step, program, drainFirstCfg, emitDelimiterCfg, cfg, tapes,
    setFirst, firstPresent, clearPair, initialState]

theorem step_drainFirst_cons (keepFirst emit : Bool) (data : TapeData)
    (bit : Bool) (tail : List Bool)
    (firstEq : data.first = bit :: tail) :
    TM2.step (program keepFirst) (drainFirstCfg emit data) =
      some (drainFirstCfg emit
        { data with
          first := tail
          outputReverse :=
            if emit then .unit :: data.outputReverse
            else data.outputReverse }) := by
  rcases data with ⟨input, first, second, outputReverse, output⟩
  change first = bit :: tail at firstEq
  subst first
  cases emit <;>
    simp [TM2.step, program, drainFirstCfg, cfg, tapes, setFirst,
      firstPresent, clearPair, initialState]

theorem step_drainSecond_nil (keepFirst emit : Bool) (data : TapeData)
    (secondEq : data.second = []) :
    TM2.step (program keepFirst) (drainSecondCfg emit data) =
      some (emitDelimiterCfg { data with second := [] }) := by
  rcases data with ⟨input, first, second, outputReverse, output⟩
  change second = [] at secondEq
  subst second
  simp [TM2.step, program, drainSecondCfg, emitDelimiterCfg, cfg, tapes,
    setSecond, clearPair, initialState]

theorem step_drainSecond_cons (keepFirst emit : Bool) (data : TapeData)
    (bit : Bool) (tail : List Bool)
    (secondEq : data.second = bit :: tail) :
    TM2.step (program keepFirst) (drainSecondCfg emit data) =
      some (drainSecondCfg emit
        { data with
          second := tail
          outputReverse :=
            if emit then .unit :: data.outputReverse
            else data.outputReverse }) := by
  rcases data with ⟨input, first, second, outputReverse, output⟩
  change second = bit :: tail at secondEq
  subst second
  cases emit <;>
    simp [TM2.step, program, drainSecondCfg, cfg, tapes, setSecond,
      clearPair, initialState]

theorem step_emitDelimiter (keepFirst : Bool) (data : TapeData) :
    TM2.step (program keepFirst) (emitDelimiterCfg data) =
      some (scanCfg
        { data with outputReverse := .delimiter :: data.outputReverse }) := by
  rcases data with ⟨input, first, second, outputReverse, output⟩
  simp [TM2.step, program, emitDelimiterCfg, scanCfg, cfg, tapes,
    initialState]

theorem step_reverseOutput_nil (keepFirst : Bool)
    (output : List UnaryFieldEncoderMachine.Symbol) :
    TM2.step (program keepFirst)
        (reverseOutputCfg ⟨[], [], [], [], output⟩) =
      some (haltCfg output) := by
  simp [TM2.step, program, reverseOutputCfg, haltCfg, cfg, tapes,
    setOutput, clearOutput, initialState]

theorem step_reverseOutput_cons (keepFirst : Bool) (data : TapeData)
    (symbol : UnaryFieldEncoderMachine.Symbol)
    (tail : List UnaryFieldEncoderMachine.Symbol)
    (outputReverseEq : data.outputReverse = symbol :: tail) :
    TM2.step (program keepFirst) (reverseOutputCfg data) =
      some (reverseOutputCfg
        { data with
          outputReverse := tail
          output := symbol :: data.output }) := by
  rcases data with ⟨input, first, second, outputReverse, output⟩
  change outputReverse = symbol :: tail at outputReverseEq
  subst outputReverse
  simp [TM2.step, program, reverseOutputCfg, cfg, tapes, setOutput,
    outputFromState, clearOutput, initialState]

end DelimitedBinaryWordPairExcessMachine
end LeanTrominoes
