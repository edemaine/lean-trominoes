/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairProductPairWordExecution

/-! # One-pair execution for the binary-word ordered-product machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairProductMachine

def pairTime (first second : List Bool) : Nat :=
  2 * first.length + second.length + 4

def pair_evalsInTime (first second : List Bool) (tail : List WordToken)
    (data : TapeData)
    (sourceEq : data.source =
      DelimitedBinaryWords.wordTokens second ++ tail)
    (firstEq : data.first = [])
    (firstOriginalEq : data.firstOriginal = first) :
    EvalsToInTime (TM2.step program) (scanInnerCfg data)
      (some (scanInnerCfg
        { data with
          source := tail
          first := []
          firstOriginal := first
          sourceRestore :=
            (DelimitedBinaryWords.wordTokens second).reverse ++
              data.sourceRestore
          outputReverse :=
            (DelimitedBinaryWordPairs.pairTokens
              (first, second)).reverse ++ data.outputReverse }))
      (pairTime first second) := by
  let secondTail :=
    second.map DelimitedBinaryWords.Token.bit ++
      DelimitedBinaryWords.Token.wordEnd :: tail
  let afterStart : TapeData :=
    { data with
      source := secondTail
      sourceRestore :=
        DelimitedBinaryWords.Token.wordStart :: data.sourceRestore
      outputReverse :=
        DelimitedBinaryWordPairs.Token.pairStart :: data.outputReverse }
  let afterFirst : TapeData :=
    { afterStart with
      first := first.reverse
      firstOriginal := []
      outputReverse :=
        DelimitedBinaryWordPairs.Token.middle ::
          (first.map
            DelimitedBinaryWordPairs.Token.firstBit).reverse ++
            afterStart.outputReverse }
  let afterSecond : TapeData :=
    { afterFirst with
      source := tail
      sourceRestore :=
        (second.map DelimitedBinaryWords.Token.bit ++
          [DelimitedBinaryWords.Token.wordEnd]).reverse ++
            afterFirst.sourceRestore
      outputReverse :=
        DelimitedBinaryWordPairs.Token.pairEnd ::
          (second.map
            DelimitedBinaryWordPairs.Token.secondBit).reverse ++
            afterFirst.outputReverse }
  have sourceEq' : data.source = .wordStart :: secondTail := by
    simpa [DelimitedBinaryWords.wordTokens, secondTail,
      List.append_assoc] using sourceEq
  have started := oneStep
    (step_scanInner_wordStart data secondTail sourceEq')
  have emitted := emitFirst_evalsInTime first afterStart (by
    simp [afterStart, firstOriginalEq])
  have scanned := scanSecond_evalsInTime second tail afterFirst (by
    simp [afterFirst, afterStart, secondTail])
  have restored := restoreFirst_evalsInTime first.reverse afterSecond (by
    simp [afterSecond, afterFirst])
  have throughFirst := EvalsToInTime.trans (TM2.step program)
    1 (first.length + 1)
    (scanInnerCfg data) (emitFirstCfg afterStart)
    (some (scanSecondCfg afterFirst))
    (by simpa [afterStart] using started)
    (by simpa [afterFirst, afterStart, firstEq] using emitted)
  have throughSecond := EvalsToInTime.trans (TM2.step program)
    (first.length + 2) (second.length + 1)
    (scanInnerCfg data) (scanSecondCfg afterFirst)
    (some (restoreFirstCfg afterSecond)) throughFirst
    (by simpa [afterSecond] using scanned)
  have composed := EvalsToInTime.trans (TM2.step program)
    (first.length + second.length + 3) (first.reverse.length + 1)
    (scanInnerCfg data) (restoreFirstCfg afterSecond)
    (some (scanInnerCfg
      { afterSecond with
        first := []
        firstOriginal := first.reverse.reverse ++
          afterSecond.firstOriginal }))
    (by
      convert throughSecond using 1
      omega)
    restored
  convert composed using 1
  · simp [afterSecond, afterFirst, afterStart,
      DelimitedBinaryWords.wordTokens,
      DelimitedBinaryWordPairs.pairTokens,
      List.reverse_append, List.append_assoc]
  · simp [pairTime]
    omega

end DelimitedBinaryWordPairProductMachine
end LeanTrominoes
