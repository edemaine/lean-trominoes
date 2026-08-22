/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryBlockRightRotationOutputSemantics
import LeanTrominoes.UnaryBlockRightRotationParsing

/-! # Complete parsing and scanning for unary block right rotation -/

noncomputable section

namespace LeanTrominoes.UnaryBlockRightRotationMachine

open StateTransition Turing

def scanTime (input : Input) : Nat :=
  1 + fieldsTime input.groupSizes input.blockStarts +
    parseTime
      (UnaryFieldEncoderMachine.unaryFields input.groupSizes)
      (UnaryFieldEncoderMachine.unaryFields input.blockStarts)

def scan_evalsInTime (input : Input) :
    EvalsToInTime machine.step
      (scanLeftCfg
        ⟨encode input, [], [], [], [], [], [], [], [], [], [], [], []⟩)
      (some (reverseOutputCfg
        ⟨[], [], [], [], [], [], [], [], [], [], [],
          (outputEncoding input).reverse, []⟩))
      (scanTime input) := by
  let sizes := UnaryFieldEncoderMachine.unaryFields input.groupSizes
  let starts := UnaryFieldEncoderMachine.unaryFields input.blockStarts
  let startData : TapeData :=
    ⟨encode input, [], [], [], [], [], [], [], [], [], [], [], []⟩
  let parsedData : TapeData :=
    ⟨[], [], sizes, [], starts, [], [], [], [], [], [], [], []⟩
  let processedData : TapeData :=
    ⟨[], [], [], [], [], [], [], [], [], [], [],
      (outputEncoding input).reverse, []⟩
  have parseRun := parsing_evalsInTime sizes starts
  have parseRun' : EvalsToInTime machine.step (scanLeftCfg startData)
      (some (scanSizeFieldCfg parsedData)) (parseTime sizes starts) := by
    simpa [startData, parsedData, sizes, starts, encode,
      SeparatedProductEncoding.encode] using parseRun
  have fieldsRun := fields_evalsInTime input.valid parsedData
    (by simp [parsedData, sizes])
    (by simp [parsedData, starts]) rfl rfl rfl rfl rfl rfl
  have fieldsRun' : EvalsToInTime machine.step
      (scanSizeFieldCfg parsedData)
      (some (scanSizeFieldCfg processedData))
      (fieldsTime input.groupSizes input.blockStarts) := by
    simpa [parsedData, processedData, sizes, starts, outputEncoding,
      blocksOutputReverse_eq input.valid] using fieldsRun
  have throughFields := EvalsToInTime.trans machine.step
    (parseTime sizes starts)
    (fieldsTime input.groupSizes input.blockStarts)
    _ _ _ parseRun' fieldsRun'
  have finish := oneStep (step_scanSizeField_nil processedData rfl)
  have whole := EvalsToInTime.trans machine.step
    (fieldsTime input.groupSizes input.blockStarts +
      parseTime sizes starts) 1
    _ _ _ throughFields finish
  simpa [startData, processedData, scanTime, sizes, starts,
    Nat.add_assoc] using whole

end LeanTrominoes.UnaryBlockRightRotationMachine

end
