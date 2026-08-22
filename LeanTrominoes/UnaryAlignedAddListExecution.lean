/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryAlignedAddFieldExecution

/-! # Executing aligned lists of unary additions -/

noncomputable section

namespace LeanTrominoes
namespace UnaryAlignedAddMachine

open StateTransition Turing

def fields_evalsInTime (firsts seconds : List Nat)
    (firstsTail secondsTail : List UnarySymbol) (data : TapeData)
    (valid : Valid firsts seconds)
    (firstsEq : data.firsts =
      UnaryFieldEncoderMachine.unaryFields firsts ++ firstsTail)
    (secondsEq : data.seconds =
      UnaryFieldEncoderMachine.unaryFields seconds ++ secondsTail) :
    EvalsToInTime machine.step (scanFirstFieldCfg data)
      (some (scanFirstFieldCfg
        { data with
          firsts := firstsTail
          seconds := secondsTail
          outputReverse :=
            (UnaryFieldEncoderMachine.unaryFields
              (sums firsts seconds)).reverse ++ data.outputReverse }))
      (fieldsTime firsts seconds) := by
  induction valid generalizing data with
  | nil =>
      rcases data with
        ⟨input, firstReverse, firstTokens, secondReverse, secondTokens,
          outputReverse, output⟩
      change firstTokens =
        UnaryFieldEncoderMachine.unaryFields [] ++ firstsTail at firstsEq
      change secondTokens =
        UnaryFieldEncoderMachine.unaryFields [] ++ secondsTail at secondsEq
      simp only [UnaryFieldEncoderMachine.unaryFields_nil,
        List.nil_append] at firstsEq secondsEq
      subst firstTokens
      subst secondTokens
      have zero := EvalsToInTime.refl machine.step
        (scanFirstFieldCfg
          ⟨input, firstReverse, firstsTail, secondReverse, secondsTail,
            outputReverse, output⟩)
      simpa [fieldsTime, sums] using zero
  | @cons first second firsts seconds valid induction =>
      let firstsRemaining : List UnarySymbol :=
        UnaryFieldEncoderMachine.unaryFields firsts ++ firstsTail
      let secondsRemaining : List UnarySymbol :=
        UnaryFieldEncoderMachine.unaryFields seconds ++ secondsTail
      let nextData : TapeData :=
        { data with
          firsts := firstsRemaining
          seconds := secondsRemaining
          outputReverse :=
            (UnaryFieldEncoderMachine.unaryField
              (first + second)).reverse ++ data.outputReverse }
      have firstFieldEq : data.firsts =
          UnaryFieldEncoderMachine.unaryField first ++ firstsRemaining := by
        simpa [firstsRemaining,
          UnaryFieldEncoderMachine.unaryFields_cons,
          List.append_assoc] using firstsEq
      have secondFieldEq : data.seconds =
          UnaryFieldEncoderMachine.unaryField second ++ secondsRemaining := by
        simpa [secondsRemaining,
          UnaryFieldEncoderMachine.unaryFields_cons,
          List.append_assoc] using secondsEq
      have firstExecution := field_evalsInTime first second
        firstsRemaining secondsRemaining data firstFieldEq secondFieldEq
      have firstExecution' : EvalsToInTime machine.step
          (scanFirstFieldCfg data) (some (scanFirstFieldCfg nextData))
          (fieldTime first second) := by
        simpa [nextData] using firstExecution
      have rest := induction nextData rfl rfl
      have whole := EvalsToInTime.trans machine.step
        (fieldTime first second) (fieldsTime firsts seconds)
        _ _ _ firstExecution' rest
      simpa [nextData, fieldsTime, sums,
        UnaryFieldEncoderMachine.unaryFields_cons,
        List.reverse_append, List.append_assoc,
        Nat.add_comm] using whole

end UnaryAlignedAddMachine
end LeanTrominoes
