/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryAlignedAddExecutionSupport
import LeanTrominoes.UnaryAlignedAddFirstFieldSteps

/-! # First-field copying for aligned unary addition -/

noncomputable section

namespace LeanTrominoes
namespace UnaryAlignedAddMachine

open StateTransition Turing

def copyFirst_evalsInTime (count : Nat) (tail : List UnarySymbol)
    (data : TapeData)
    (firstsEq : data.firsts =
      UnaryFieldEncoderMachine.unaryField count ++ tail) :
    EvalsToInTime machine.step (scanFirstFieldCfg data)
      (some (scanSecondFieldCfg
        { data with
          firsts := tail
          outputReverse :=
            List.replicate count .unit ++ data.outputReverse }))
      (2 * count + 1) := by
  induction count generalizing data with
  | zero =>
      have step := step_scanFirstField_delimiter data tail
        (by simpa [UnaryFieldEncoderMachine.unaryField] using firstsEq)
      simpa using oneStep step
  | succ count induction =>
      have firstsHead : data.firsts = .unit ::
          (UnaryFieldEncoderMachine.unaryField count ++ tail) := by
        simpa [UnaryFieldEncoderMachine.unaryField,
          List.replicate_succ] using firstsEq
      let popped := oneStep
        (step_scanFirstField_unit data
          (UnaryFieldEncoderMachine.unaryField count ++ tail) firstsHead)
      let pushed := oneStep
        (step_pushFirstUnit
          { data with
            firsts := UnaryFieldEncoderMachine.unaryField count ++ tail })
      let nextData : TapeData :=
        { data with
          firsts := UnaryFieldEncoderMachine.unaryField count ++ tail
          outputReverse := .unit :: data.outputReverse }
      let rest := induction nextData rfl
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * count + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, List.replicate_succ, Nat.mul_add,
        replicate_unit_cons_comm, List.append_assoc,
        Nat.add_assoc] using whole

end UnaryAlignedAddMachine
end LeanTrominoes
