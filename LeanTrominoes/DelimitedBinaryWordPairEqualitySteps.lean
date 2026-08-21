/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairEqualityMachine

/-! # One-step equations for delimited binary-word equality -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairEqualityMachine

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

@[simp] theorem update_tapes_resultReverse (data : TapeData)
    (value : List Bool) :
    Function.update (tapes data) Stack.resultReverse value =
      tapes { data with resultReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_output (data : TapeData)
    (value : List Bool) :
    Function.update (tapes data) Stack.output value =
      tapes { data with output := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem step_scan_nil (data : TapeData) (inputEq : data.input = []) :
    TM2.step program (scanCfg data) =
      some (reverseCfg { data with input := [] }) := by
  rcases data with ⟨input, first, second, resultReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, scanCfg, reverseCfg, cfg, tapes,
    tokenIsNone, setToken, initialState]

theorem step_scan_pairStart (data : TapeData) (tail : List Token)
    (inputEq : data.input = .pairStart :: tail) :
    TM2.step program (scanCfg data) =
      some (readFirstCfg { data with input := tail }) := by
  rcases data with ⟨input, first, second, resultReverse, output⟩
  change input = .pairStart :: tail at inputEq
  subst input
  simp [TM2.step, program, scanCfg, readFirstCfg, cfg, tapes,
    tokenIsNone, setToken, clearToken, initialState]

theorem step_readFirst_bit (data : TapeData) (bit : Bool)
    (tail : List Token) (inputEq : data.input = .firstBit bit :: tail) :
    TM2.step program (readFirstCfg data) =
      some (readFirstCfg
        { data with
          input := tail
          first := bit :: data.first }) := by
  rcases data with ⟨input, first, second, resultReverse, output⟩
  change input = .firstBit bit :: tail at inputEq
  subst input
  simp [TM2.step, program, readFirstCfg, cfg, tapes, setToken,
    tokenIsFirstBit, tokenBitFromState, clearToken, initialState]

theorem step_readFirst_middle (data : TapeData) (tail : List Token)
    (inputEq : data.input = .middle :: tail) :
    TM2.step program (readFirstCfg data) =
      some (readSecondCfg { data with input := tail }) := by
  rcases data with ⟨input, first, second, resultReverse, output⟩
  change input = .middle :: tail at inputEq
  subst input
  simp [TM2.step, program, readFirstCfg, readSecondCfg, cfg, tapes,
    setToken, tokenIsFirstBit, clearToken, initialState]

theorem step_readSecond_bit (data : TapeData) (bit : Bool)
    (tail : List Token) (inputEq : data.input = .secondBit bit :: tail) :
    TM2.step program (readSecondCfg data) =
      some (readSecondCfg
        { data with
          input := tail
          second := bit :: data.second }) := by
  rcases data with ⟨input, first, second, resultReverse, output⟩
  change input = .secondBit bit :: tail at inputEq
  subst input
  simp [TM2.step, program, readSecondCfg, cfg, tapes, setToken,
    tokenIsSecondBit, tokenBitFromState, clearToken, initialState]

theorem step_readSecond_pairEnd (data : TapeData) (tail : List Token)
    (inputEq : data.input = .pairEnd :: tail) :
    TM2.step program (readSecondCfg data) =
      some (compareCfg true { data with input := tail }) := by
  rcases data with ⟨input, first, second, resultReverse, output⟩
  change input = .pairEnd :: tail at inputEq
  subst input
  simp [TM2.step, program, readSecondCfg, compareCfg, cfg, tapes,
    setToken, tokenIsSecondBit, clearToken, initialState]

theorem step_compare_nil_nil (equal : Bool) (data : TapeData)
    (firstEq : data.first = []) (secondEq : data.second = []) :
    TM2.step program (compareCfg equal data) =
      some (scanCfg
        { data with
          first := []
          second := []
          resultReverse := equal :: data.resultReverse }) := by
  rcases data with ⟨input, first, second, resultReverse, output⟩
  change first = [] at firstEq
  change second = [] at secondEq
  subst first
  subst second
  simp [TM2.step, program, compareCfg, scanCfg, cfg, tapes, setFirst,
    setSecond, bothWordsEmpty, equalityFromState, initialState]

theorem step_compare_cons_cons (equal firstBit secondBit : Bool)
    (data : TapeData) (firstTail secondTail : List Bool)
    (firstEq : data.first = firstBit :: firstTail)
    (secondEq : data.second = secondBit :: secondTail) :
    TM2.step program (compareCfg equal data) =
      some (compareCfg (equal && decide (firstBit = secondBit))
        { data with
          first := firstTail
          second := secondTail }) := by
  rcases data with ⟨input, first, second, resultReverse, output⟩
  change first = firstBit :: firstTail at firstEq
  change second = secondBit :: secondTail at secondEq
  subst first
  subst second
  simp [TM2.step, program, compareCfg, cfg, tapes, setFirst, setSecond,
    bothWordsEmpty, advanceCompare]

theorem step_compare_cons_nil (equal firstBit : Bool) (data : TapeData)
    (firstTail : List Bool) (firstEq : data.first = firstBit :: firstTail)
    (secondEq : data.second = []) :
    TM2.step program (compareCfg equal data) =
      some (compareCfg false
        { data with
          first := firstTail
          second := [] }) := by
  rcases data with ⟨input, first, second, resultReverse, output⟩
  change first = firstBit :: firstTail at firstEq
  change second = [] at secondEq
  subst first
  subst second
  simp [TM2.step, program, compareCfg, cfg, tapes, setFirst, setSecond,
    bothWordsEmpty, advanceCompare]

theorem step_compare_nil_cons (equal secondBit : Bool) (data : TapeData)
    (secondTail : List Bool) (firstEq : data.first = [])
    (secondEq : data.second = secondBit :: secondTail) :
    TM2.step program (compareCfg equal data) =
      some (compareCfg false
        { data with
          first := []
          second := secondTail }) := by
  rcases data with ⟨input, first, second, resultReverse, output⟩
  change first = [] at firstEq
  change second = secondBit :: secondTail at secondEq
  subst first
  subst second
  simp [TM2.step, program, compareCfg, cfg, tapes, setFirst, setSecond,
    bothWordsEmpty, advanceCompare]

theorem step_reverse_nil (output : List Bool) :
    TM2.step program
        (reverseCfg ⟨[], [], [], [], output⟩) =
      some (haltCfg output) := by
  simp [TM2.step, program, reverseCfg, haltCfg, cfg, tapes, setFirst,
    initialState]

theorem step_reverse_cons (data : TapeData) (bit : Bool)
    (tail : List Bool) (resultReverseEq : data.resultReverse = bit :: tail) :
    TM2.step program (reverseCfg data) =
      some (reverseCfg
        { data with
          resultReverse := tail
          output := bit :: data.output }) := by
  rcases data with ⟨input, first, second, resultReverse, output⟩
  change resultReverse = bit :: tail at resultReverseEq
  subst resultReverse
  simp [TM2.step, program, reverseCfg, cfg, tapes, setFirst,
    firstBitFromState, clearFirst, initialState]

end DelimitedBinaryWordPairEqualityMachine
end LeanTrominoes
