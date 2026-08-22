/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryAlignedAddCopyFirstExecution
import LeanTrominoes.UnaryAlignedAddCopySecondExecution
import LeanTrominoes.UnaryAlignedAddInput

/-! # Complete field execution for aligned unary addition -/

noncomputable section

namespace LeanTrominoes
namespace UnaryAlignedAddMachine

open StateTransition Turing

def field_evalsInTime (first second : Nat)
    (firstsTail secondsTail : List UnarySymbol) (data : TapeData)
    (firstsEq : data.firsts =
      UnaryFieldEncoderMachine.unaryField first ++ firstsTail)
    (secondsEq : data.seconds =
      UnaryFieldEncoderMachine.unaryField second ++ secondsTail) :
    EvalsToInTime machine.step (scanFirstFieldCfg data)
      (some (scanFirstFieldCfg
        { data with
          firsts := firstsTail
          seconds := secondsTail
          outputReverse :=
            (UnaryFieldEncoderMachine.unaryField
              (first + second)).reverse ++ data.outputReverse }))
      (fieldTime first second) := by
  let afterFirst : TapeData :=
    { data with
      firsts := firstsTail
      outputReverse :=
        List.replicate first .unit ++ data.outputReverse }
  let afterSecond : TapeData :=
    { afterFirst with
      seconds := secondsTail
      outputReverse :=
        List.replicate second .unit ++ afterFirst.outputReverse }
  have copiedFirst := copyFirst_evalsInTime first firstsTail data firstsEq
  have copiedFirst' : EvalsToInTime machine.step (scanFirstFieldCfg data)
      (some (scanSecondFieldCfg afterFirst)) (2 * first + 1) := by
    simpa [afterFirst] using copiedFirst
  have copiedSecond := copySecond_evalsInTime second secondsTail
    afterFirst (by simpa [afterFirst] using secondsEq)
  have copiedSecond' : EvalsToInTime machine.step
      (scanSecondFieldCfg afterFirst)
      (some (emitDelimiterCfg afterSecond)) (2 * second + 1) := by
    simpa [afterSecond] using copiedSecond
  have delimited := oneStep (step_emitDelimiter afterSecond)
  have throughFields := EvalsToInTime.trans machine.step
    (2 * first + 1) (2 * second + 1) _ _ _
    copiedFirst' copiedSecond'
  have whole := EvalsToInTime.trans machine.step
    (2 * second + 1 + (2 * first + 1)) 1 _ _ _
    throughFields delimited
  have outputReverseEq :
      .delimiter ::
          (List.replicate second (.unit : UnarySymbol) ++
            List.replicate first .unit ++ data.outputReverse) =
        (UnaryFieldEncoderMachine.unaryField
          (first + second)).reverse ++ data.outputReverse := by
    rw [← List.replicate_add]
    have countsEq : second + first = first + second := Nat.add_comm _ _
    rw [countsEq]
    simp [UnaryFieldEncoderMachine.unaryField, List.reverse_append]
  have outputReverseEq' :
      (UnaryFieldEncoderMachine.unaryField
          (first + second)).reverse ++ data.outputReverse =
        .delimiter ::
          (List.replicate second (.unit : UnarySymbol) ++
            (List.replicate first .unit ++ data.outputReverse)) := by
    rw [← List.append_assoc]
    exact outputReverseEq.symm
  convert whole using 1
  · simp only [afterSecond, afterFirst]
    exact congrArg (fun outputReverse =>
      some (scanFirstFieldCfg
        { data with
          firsts := firstsTail
          seconds := secondsTail
          outputReverse := outputReverse }))
      outputReverseEq'
  · simp [fieldTime]
    omega

end UnaryAlignedAddMachine
end LeanTrominoes
