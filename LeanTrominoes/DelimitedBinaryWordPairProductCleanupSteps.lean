/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairProductTapeUpdates

/-! # Cleanup steps for the binary-word ordered-product machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairProductMachine

theorem step_restoreSource_nil (data : TapeData)
    (sourceRestoreEq : data.sourceRestore = []) :
    TM2.step program (restoreSourceCfg data) =
      some (clearFirstCfg { data with sourceRestore := [] }) := by
  rcases data with
    ⟨input, reverse, outer, source, first, firstOriginal,
      sourceRestore, outputReverse, output⟩
  change sourceRestore = [] at sourceRestoreEq
  subst sourceRestore
  simp [TM2.step, program, restoreSourceCfg, clearFirstCfg, cfg, tapes,
    setWordToken, wordTokenIsNone, clearWordToken, initialState]

theorem step_restoreSource_cons (data : TapeData) (token : WordToken)
    (tail : List WordToken)
    (sourceRestoreEq : data.sourceRestore = token :: tail) :
    TM2.step program (restoreSourceCfg data) =
      some (restoreSourceCfg
        { data with
          source := token :: data.source
          sourceRestore := tail }) := by
  rcases data with
    ⟨input, reverse, outer, source, first, firstOriginal,
      sourceRestore, outputReverse, output⟩
  change sourceRestore = token :: tail at sourceRestoreEq
  subst sourceRestore
  simp [TM2.step, program, restoreSourceCfg, cfg, tapes, setWordToken,
    wordTokenIsNone, wordTokenFromState, clearWordToken, initialState]

theorem step_clearFirst_nil (data : TapeData)
    (firstOriginalEq : data.firstOriginal = []) :
    TM2.step program (clearFirstCfg data) =
      some (scanOuterCfg { data with firstOriginal := [] }) := by
  rcases data with
    ⟨input, reverse, outer, source, first, firstOriginal,
      sourceRestore, outputReverse, output⟩
  change firstOriginal = [] at firstOriginalEq
  subst firstOriginal
  simp [TM2.step, program, clearFirstCfg, scanOuterCfg, cfg, tapes,
    setBit, bitIsNone, clearBit, initialState]

theorem step_clearFirst_cons (data : TapeData) (bit : Bool)
    (tail : List Bool)
    (firstOriginalEq : data.firstOriginal = bit :: tail) :
    TM2.step program (clearFirstCfg data) =
      some (clearFirstCfg { data with firstOriginal := tail }) := by
  rcases data with
    ⟨input, reverse, outer, source, first, firstOriginal,
      sourceRestore, outputReverse, output⟩
  change firstOriginal = bit :: tail at firstOriginalEq
  subst firstOriginal
  simp [TM2.step, program, clearFirstCfg, cfg, tapes, setBit,
    bitIsNone, clearBit, initialState]

theorem step_clearSource_nil (data : TapeData)
    (sourceEq : data.source = []) :
    TM2.step program (clearSourceCfg data) =
      some (reverseOutputCfg { data with source := [] }) := by
  rcases data with
    ⟨input, reverse, outer, source, first, firstOriginal,
      sourceRestore, outputReverse, output⟩
  change source = [] at sourceEq
  subst source
  simp [TM2.step, program, clearSourceCfg, reverseOutputCfg, cfg, tapes,
    setWordToken, wordTokenIsNone, clearWordToken, initialState]

theorem step_clearSource_cons (data : TapeData) (token : WordToken)
    (tail : List WordToken) (sourceEq : data.source = token :: tail) :
    TM2.step program (clearSourceCfg data) =
      some (clearSourceCfg { data with source := tail }) := by
  rcases data with
    ⟨input, reverse, outer, source, first, firstOriginal,
      sourceRestore, outputReverse, output⟩
  change source = token :: tail at sourceEq
  subst source
  simp [TM2.step, program, clearSourceCfg, cfg, tapes, setWordToken,
    wordTokenIsNone, clearWordToken, initialState]

theorem step_reverseOutput_nil (output : List PairToken) :
    TM2.step program
        (reverseOutputCfg ⟨[], [], [], [], [], [], [], [], output⟩) =
      some (haltCfg output) := by
  simp [TM2.step, program, reverseOutputCfg, haltCfg, cfg, tapes,
    setPairToken, clearPairToken, initialState]

theorem step_reverseOutput_cons (data : TapeData) (token : PairToken)
    (tail : List PairToken)
    (outputReverseEq : data.outputReverse = token :: tail) :
    TM2.step program (reverseOutputCfg data) =
      some (reverseOutputCfg
        { data with
          outputReverse := tail
          output := token :: data.output }) := by
  rcases data with
    ⟨input, reverse, outer, source, first, firstOriginal,
      sourceRestore, outputReverse, output⟩
  change outputReverse = token :: tail at outputReverseEq
  subst outputReverse
  simp [TM2.step, program, reverseOutputCfg, cfg, tapes, setPairToken,
    pairTokenFromState, clearPairToken, initialState]

end DelimitedBinaryWordPairProductMachine
end LeanTrominoes
