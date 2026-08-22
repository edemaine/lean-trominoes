/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryBlockRightRotationExecutionSupport
import LeanTrominoes.UnaryBlockRightRotationFieldSteps

/-! # Scanning unary size and start fields for block right rotation -/

noncomputable section

namespace LeanTrominoes.UnaryBlockRightRotationMachine

open StateTransition Turing

def scanSizeField_evalsInTime (count : Nat) (tail : List UnarySymbol)
    (data : TapeData)
    (sizesEq : data.sizes =
      UnaryFieldEncoderMachine.unaryField count ++ tail) :
    EvalsToInTime machine.step (scanSizeFieldCfg data)
      (some (scanStartFieldCfg
        { data with
          sizes := tail
          group := List.replicate count () ++ data.group }))
      (2 * count + 1) := by
  induction count generalizing data with
  | zero =>
      have step := step_scanSizeField_delimiter data tail
        (by simpa [UnaryFieldEncoderMachine.unaryField] using sizesEq)
      simpa using oneStep step
  | succ count induction =>
      have sizesHead : data.sizes = .unit ::
          (UnaryFieldEncoderMachine.unaryField count ++ tail) := by
        simpa [UnaryFieldEncoderMachine.unaryField,
          List.replicate_succ] using sizesEq
      let popped := oneStep
        (step_scanSizeField_unit data
          (UnaryFieldEncoderMachine.unaryField count ++ tail) sizesHead)
      let nextData : TapeData :=
        { data with
          sizes := UnaryFieldEncoderMachine.unaryField count ++ tail
          group := () :: data.group }
      let pushed := oneStep
        (step_pushGroupUnit
          { data with
            sizes := UnaryFieldEncoderMachine.unaryField count ++ tail })
      let rest := induction nextData rfl
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * count + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, List.replicate_succ, Nat.mul_add,
        replicate_value_cons_comm, List.append_assoc,
        Nat.add_assoc] using whole

def scanStartField_evalsInTime (count : Nat) (tail : List UnarySymbol)
    (data : TapeData)
    (startsEq : data.starts =
      UnaryFieldEncoderMachine.unaryField count ++ tail) :
    EvalsToInTime machine.step (scanStartFieldCfg data)
      (some (beginGroupCfg
        { data with
          starts := tail
          start := List.replicate count () ++ data.start }))
      (2 * count + 1) := by
  induction count generalizing data with
  | zero =>
      have step := step_scanStartField_delimiter data tail
        (by simpa [UnaryFieldEncoderMachine.unaryField] using startsEq)
      simpa using oneStep step
  | succ count induction =>
      have startsHead : data.starts = .unit ::
          (UnaryFieldEncoderMachine.unaryField count ++ tail) := by
        simpa [UnaryFieldEncoderMachine.unaryField,
          List.replicate_succ] using startsEq
      let popped := oneStep
        (step_scanStartField_unit data
          (UnaryFieldEncoderMachine.unaryField count ++ tail) startsHead)
      let nextData : TapeData :=
        { data with
          starts := UnaryFieldEncoderMachine.unaryField count ++ tail
          start := () :: data.start }
      let pushed := oneStep
        (step_pushStartUnit
          { data with
            starts := UnaryFieldEncoderMachine.unaryField count ++ tail })
      let rest := induction nextData rfl
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let whole := EvalsToInTime.trans machine.step
        2 (2 * count + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, List.replicate_succ, Nat.mul_add,
        replicate_value_cons_comm, List.append_assoc,
        Nat.add_assoc] using whole

end LeanTrominoes.UnaryBlockRightRotationMachine

end
