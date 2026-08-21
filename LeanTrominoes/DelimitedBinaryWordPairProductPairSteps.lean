/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairProductTapeUpdates

/-! # Pair-emission steps for the binary-word product machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairProductMachine

theorem step_scanInner_nil (data : TapeData) (sourceEq : data.source = []) :
    TM2.step program (scanInnerCfg data) =
      some (restoreSourceCfg { data with source := [] }) := by
  rcases data with
    ⟨input, reverse, outer, source, first, firstOriginal,
      sourceRestore, outputReverse, output⟩
  change source = [] at sourceEq
  subst source
  simp [TM2.step, program, scanInnerCfg, restoreSourceCfg, cfg, tapes,
    setWordToken, wordTokenIsNone, clearWordToken, initialState]

theorem step_scanInner_wordStart (data : TapeData)
    (tail : List WordToken) (sourceEq : data.source = .wordStart :: tail) :
    TM2.step program (scanInnerCfg data) =
      some (emitFirstCfg
        { data with
          source := tail
          sourceRestore := .wordStart :: data.sourceRestore
          outputReverse :=
            DelimitedBinaryWordPairs.Token.pairStart ::
              data.outputReverse }) := by
  rcases data with
    ⟨input, reverse, outer, source, first, firstOriginal,
      sourceRestore, outputReverse, output⟩
  change source = .wordStart :: tail at sourceEq
  subst source
  simp [TM2.step, program, scanInnerCfg, emitFirstCfg, cfg, tapes,
    setWordToken, wordTokenIsNone, wordTokenFromState, clearWordToken,
    initialState]

theorem step_emitFirst_nil (data : TapeData)
    (firstOriginalEq : data.firstOriginal = []) :
    TM2.step program (emitFirstCfg data) =
      some (scanSecondCfg
        { data with
          firstOriginal := []
          outputReverse :=
            DelimitedBinaryWordPairs.Token.middle ::
              data.outputReverse }) := by
  rcases data with
    ⟨input, reverse, outer, source, first, firstOriginal,
      sourceRestore, outputReverse, output⟩
  change firstOriginal = [] at firstOriginalEq
  subst firstOriginal
  simp [TM2.step, program, emitFirstCfg, scanSecondCfg, cfg, tapes,
    setBit, bitIsNone, clearBit, initialState]

theorem step_emitFirst_cons (data : TapeData) (bit : Bool)
    (tail : List Bool)
    (firstOriginalEq : data.firstOriginal = bit :: tail) :
    TM2.step program (emitFirstCfg data) =
      some (emitFirstCfg
        { data with
          first := bit :: data.first
          firstOriginal := tail
          outputReverse :=
            DelimitedBinaryWordPairs.Token.firstBit bit ::
              data.outputReverse }) := by
  rcases data with
    ⟨input, reverse, outer, source, first, firstOriginal,
      sourceRestore, outputReverse, output⟩
  change firstOriginal = bit :: tail at firstOriginalEq
  subst firstOriginal
  simp [TM2.step, program, emitFirstCfg, cfg, tapes, setBit,
    bitIsNone, firstBitTokenFromState, bitFromState, clearBit,
    initialState]

theorem step_scanSecond_bit (data : TapeData) (bit : Bool)
    (tail : List WordToken) (sourceEq : data.source = .bit bit :: tail) :
    TM2.step program (scanSecondCfg data) =
      some (scanSecondCfg
        { data with
          source := tail
          sourceRestore := .bit bit :: data.sourceRestore
          outputReverse :=
            DelimitedBinaryWordPairs.Token.secondBit bit ::
              data.outputReverse }) := by
  rcases data with
    ⟨input, reverse, outer, source, first, firstOriginal,
      sourceRestore, outputReverse, output⟩
  change source = .bit bit :: tail at sourceEq
  subst source
  simp [TM2.step, program, scanSecondCfg, cfg, tapes, setWordToken,
    wordTokenIsBit, wordTokenFromState, secondBitTokenFromState,
    wordBitFromState, clearWordToken, initialState]

theorem step_scanSecond_wordEnd (data : TapeData)
    (tail : List WordToken) (sourceEq : data.source = .wordEnd :: tail) :
    TM2.step program (scanSecondCfg data) =
      some (restoreFirstCfg
        { data with
          source := tail
          sourceRestore := .wordEnd :: data.sourceRestore
          outputReverse :=
            DelimitedBinaryWordPairs.Token.pairEnd ::
              data.outputReverse }) := by
  rcases data with
    ⟨input, reverse, outer, source, first, firstOriginal,
      sourceRestore, outputReverse, output⟩
  change source = .wordEnd :: tail at sourceEq
  subst source
  simp [TM2.step, program, scanSecondCfg, restoreFirstCfg, cfg, tapes,
    setWordToken, wordTokenIsBit, wordTokenFromState, clearWordToken,
    initialState]

theorem step_restoreFirst_nil (data : TapeData)
    (firstEq : data.first = []) :
    TM2.step program (restoreFirstCfg data) =
      some (scanInnerCfg { data with first := [] }) := by
  rcases data with
    ⟨input, reverse, outer, source, first, firstOriginal,
      sourceRestore, outputReverse, output⟩
  change first = [] at firstEq
  subst first
  simp [TM2.step, program, restoreFirstCfg, scanInnerCfg, cfg, tapes,
    setBit, bitIsNone, clearBit, initialState]

theorem step_restoreFirst_cons (data : TapeData) (bit : Bool)
    (tail : List Bool) (firstEq : data.first = bit :: tail) :
    TM2.step program (restoreFirstCfg data) =
      some (restoreFirstCfg
        { data with
          first := tail
          firstOriginal := bit :: data.firstOriginal }) := by
  rcases data with
    ⟨input, reverse, outer, source, first, firstOriginal,
      sourceRestore, outputReverse, output⟩
  change first = bit :: tail at firstEq
  subst first
  simp [TM2.step, program, restoreFirstCfg, cfg, tapes, setBit,
    bitIsNone, bitFromState, clearBit, initialState]

end DelimitedBinaryWordPairProductMachine
end LeanTrominoes
