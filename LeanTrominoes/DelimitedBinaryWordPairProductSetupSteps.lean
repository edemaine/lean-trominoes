/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairProductTapeUpdates

/-! # Setup steps for the binary-word ordered-product machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairProductMachine

theorem step_copyInput_nil (data : TapeData) (inputEq : data.input = []) :
    TM2.step program (copyInputCfg data) =
      some (duplicateCfg { data with input := [] }) := by
  rcases data with
    ⟨input, reverse, outer, source, first, firstOriginal,
      sourceRestore, outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, copyInputCfg, duplicateCfg, cfg, tapes,
    setWordToken, wordTokenIsNone, clearWordToken, initialState]

theorem step_copyInput_cons (data : TapeData) (token : WordToken)
    (tail : List WordToken) (inputEq : data.input = token :: tail) :
    TM2.step program (copyInputCfg data) =
      some (copyInputCfg
        { data with
          input := tail
          reverse := token :: data.reverse }) := by
  rcases data with
    ⟨input, reverse, outer, source, first, firstOriginal,
      sourceRestore, outputReverse, output⟩
  change input = token :: tail at inputEq
  subst input
  simp [TM2.step, program, copyInputCfg, cfg, tapes, setWordToken,
    wordTokenIsNone, wordTokenFromState, clearWordToken, initialState]

theorem step_duplicate_nil (data : TapeData)
    (reverseEq : data.reverse = []) :
    TM2.step program (duplicateCfg data) =
      some (scanOuterCfg { data with reverse := [] }) := by
  rcases data with
    ⟨input, reverse, outer, source, first, firstOriginal,
      sourceRestore, outputReverse, output⟩
  change reverse = [] at reverseEq
  subst reverse
  simp [TM2.step, program, duplicateCfg, scanOuterCfg, cfg, tapes,
    setWordToken, wordTokenIsNone, clearWordToken, initialState]

theorem step_duplicate_cons (data : TapeData) (token : WordToken)
    (tail : List WordToken) (reverseEq : data.reverse = token :: tail) :
    TM2.step program (duplicateCfg data) =
      some (duplicateCfg
        { data with
          reverse := tail
          outer := token :: data.outer
          source := token :: data.source }) := by
  rcases data with
    ⟨input, reverse, outer, source, first, firstOriginal,
      sourceRestore, outputReverse, output⟩
  change reverse = token :: tail at reverseEq
  subst reverse
  simp [TM2.step, program, duplicateCfg, cfg, tapes, setWordToken,
    wordTokenIsNone, wordTokenFromState, clearWordToken, initialState]

theorem step_scanOuter_nil (data : TapeData) (outerEq : data.outer = []) :
    TM2.step program (scanOuterCfg data) =
      some (clearSourceCfg { data with outer := [] }) := by
  rcases data with
    ⟨input, reverse, outer, source, first, firstOriginal,
      sourceRestore, outputReverse, output⟩
  change outer = [] at outerEq
  subst outer
  simp [TM2.step, program, scanOuterCfg, clearSourceCfg, cfg, tapes,
    setWordToken, wordTokenIsNone, clearWordToken, initialState]

theorem step_scanOuter_wordStart (data : TapeData) (tail : List WordToken)
    (outerEq : data.outer = .wordStart :: tail) :
    TM2.step program (scanOuterCfg data) =
      some (readOuterCfg { data with outer := tail }) := by
  rcases data with
    ⟨input, reverse, outer, source, first, firstOriginal,
      sourceRestore, outputReverse, output⟩
  change outer = .wordStart :: tail at outerEq
  subst outer
  simp [TM2.step, program, scanOuterCfg, readOuterCfg, cfg, tapes,
    setWordToken, wordTokenIsNone, clearWordToken, initialState]

theorem step_readOuter_bit (data : TapeData) (bit : Bool)
    (tail : List WordToken) (outerEq : data.outer = .bit bit :: tail) :
    TM2.step program (readOuterCfg data) =
      some (readOuterCfg
        { data with
          outer := tail
          first := bit :: data.first }) := by
  rcases data with
    ⟨input, reverse, outer, source, first, firstOriginal,
      sourceRestore, outputReverse, output⟩
  change outer = .bit bit :: tail at outerEq
  subst outer
  simp [TM2.step, program, readOuterCfg, cfg, tapes, setWordToken,
    wordTokenIsBit, wordBitFromState, clearWordToken, initialState]

theorem step_readOuter_wordEnd (data : TapeData) (tail : List WordToken)
    (outerEq : data.outer = .wordEnd :: tail) :
    TM2.step program (readOuterCfg data) =
      some (reverseFirstCfg { data with outer := tail }) := by
  rcases data with
    ⟨input, reverse, outer, source, first, firstOriginal,
      sourceRestore, outputReverse, output⟩
  change outer = .wordEnd :: tail at outerEq
  subst outer
  simp [TM2.step, program, readOuterCfg, reverseFirstCfg, cfg, tapes,
    setWordToken, wordTokenIsBit, clearWordToken, initialState]

theorem step_reverseFirst_nil (data : TapeData)
    (firstEq : data.first = []) :
    TM2.step program (reverseFirstCfg data) =
      some (scanInnerCfg { data with first := [] }) := by
  rcases data with
    ⟨input, reverse, outer, source, first, firstOriginal,
      sourceRestore, outputReverse, output⟩
  change first = [] at firstEq
  subst first
  simp [TM2.step, program, reverseFirstCfg, scanInnerCfg, cfg, tapes,
    setBit, bitIsNone, clearBit, initialState]

theorem step_reverseFirst_cons (data : TapeData) (bit : Bool)
    (tail : List Bool) (firstEq : data.first = bit :: tail) :
    TM2.step program (reverseFirstCfg data) =
      some (reverseFirstCfg
        { data with
          first := tail
          firstOriginal := bit :: data.firstOriginal }) := by
  rcases data with
    ⟨input, reverse, outer, source, first, firstOriginal,
      sourceRestore, outputReverse, output⟩
  change first = bit :: tail at firstEq
  subst first
  simp [TM2.step, program, reverseFirstCfg, cfg, tapes, setBit,
    bitIsNone, bitFromState, clearBit, initialState]

end DelimitedBinaryWordPairProductMachine
end LeanTrominoes
