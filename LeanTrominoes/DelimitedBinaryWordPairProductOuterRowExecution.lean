/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairProductOuterWordExecution
import LeanTrominoes.DelimitedBinaryWordPairProductRowExecution
import LeanTrominoes.DelimitedBinaryWordPairProductCleanupExecution

/-! # One complete outer row of the binary-word ordered product -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairProductMachine

def outerRowTime (first : List Bool) (seconds : List (List Bool)) : Nat :=
  3 * first.length +
    (seconds.flatMap DelimitedBinaryWords.wordTokens).length +
      rowTime first seconds + 5

def outerRow_evalsInTime (first : List Bool)
    (outerTail : List WordToken) (seconds : List (List Bool))
    (data : TapeData)
    (outerEq : data.outer =
      DelimitedBinaryWords.wordTokens first ++ outerTail)
    (sourceEq : data.source =
      seconds.flatMap DelimitedBinaryWords.wordTokens)
    (firstEq : data.first = [])
    (firstOriginalEq : data.firstOriginal = [])
    (sourceRestoreEq : data.sourceRestore = []) :
    EvalsToInTime (TM2.step program) (scanOuterCfg data)
      (some (scanOuterCfg
        { data with
          outer := outerTail
          source := seconds.flatMap DelimitedBinaryWords.wordTokens
          first := []
          firstOriginal := []
          sourceRestore := []
          outputReverse :=
            (rowTokens first seconds).reverse ++ data.outputReverse }))
      (outerRowTime first seconds) := by
  let sourceTokens :=
    seconds.flatMap DelimitedBinaryWords.wordTokens
  let outerBody :=
    first.map DelimitedBinaryWords.Token.bit ++
      DelimitedBinaryWords.Token.wordEnd :: outerTail
  let afterStart : TapeData := { data with outer := outerBody }
  let afterRead : TapeData :=
    { afterStart with
      outer := outerTail
      first := first.reverse }
  let afterReverse : TapeData :=
    { afterRead with
      first := []
      firstOriginal := first }
  let afterRow : TapeData :=
    { afterReverse with
      source := []
      first := []
      firstOriginal := first
      sourceRestore := sourceTokens.reverse
      outputReverse :=
        (rowTokens first seconds).reverse ++ afterReverse.outputReverse }
  let afterRestore : TapeData :=
    { afterRow with
      source := sourceTokens
      sourceRestore := [] }
  have outerEq' : data.outer = .wordStart :: outerBody := by
    simpa [DelimitedBinaryWords.wordTokens, outerBody,
      List.append_assoc] using outerEq
  have started := oneStep
    (step_scanOuter_wordStart data outerBody outerEq')
  have read := readOuter_evalsInTime first outerTail afterStart rfl
  have reversed := reverseFirst_evalsInTime first.reverse afterRead rfl
  have row := row_evalsInTime first seconds afterReverse
    (by simp [afterReverse, afterRead, afterStart, sourceEq]) rfl rfl
  have restored := restoreSource_evalsInTime sourceTokens.reverse
    afterRow rfl
  have cleared := clearFirst_evalsInTime first afterRestore rfl
  have throughRead := EvalsToInTime.trans (TM2.step program)
    1 (first.length + 1)
    (scanOuterCfg data) (readOuterCfg afterStart)
    (some (reverseFirstCfg afterRead))
    (by simpa [afterStart] using started)
    (by simpa [afterRead, afterStart, firstEq] using read)
  have throughReverse := EvalsToInTime.trans (TM2.step program)
    (first.length + 2) (first.reverse.length + 1)
    (scanOuterCfg data) (reverseFirstCfg afterRead)
    (some (scanInnerCfg afterReverse)) throughRead
    (by simpa [afterReverse, afterRead, afterStart,
      firstOriginalEq] using reversed)
  have throughRow := EvalsToInTime.trans (TM2.step program)
    (2 * first.length + 3) (rowTime first seconds)
    (scanOuterCfg data) (scanInnerCfg afterReverse)
    (some (restoreSourceCfg afterRow))
    (by
      convert throughReverse using 1
      simp only [List.length_reverse]
      omega)
    (by simpa [afterRow, afterReverse, afterRead, afterStart,
      sourceRestoreEq, sourceTokens] using row)
  have throughRestore := EvalsToInTime.trans (TM2.step program)
    (rowTime first seconds + (2 * first.length + 3))
    (sourceTokens.reverse.length + 1)
    (scanOuterCfg data) (restoreSourceCfg afterRow)
    (some (clearFirstCfg afterRestore)) throughRow
    (by simpa [afterRestore, afterRow] using restored)
  have composed := EvalsToInTime.trans (TM2.step program)
    (sourceTokens.length + 1 +
      (rowTime first seconds + (2 * first.length + 3)))
    (first.length + 1)
    (scanOuterCfg data) (clearFirstCfg afterRestore)
    (some (scanOuterCfg { afterRestore with firstOriginal := [] }))
    (by simpa [sourceTokens] using throughRestore)
    cleared
  convert composed using 1
  simp [outerRowTime, sourceTokens]
  omega

end DelimitedBinaryWordPairProductMachine
end LeanTrominoes
