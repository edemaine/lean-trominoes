/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryAlignedAddFirstFieldSteps
import LeanTrominoes.UnaryAlignedAddListExecution
import LeanTrominoes.UnaryAlignedAddParsing

/-! # Complete parsing and scanning for aligned unary addition -/

noncomputable section

namespace LeanTrominoes
namespace UnaryAlignedAddMachine

open StateTransition Turing

def scanTime (input : Input) : Nat :=
  1 + fieldsTime input.firsts input.seconds +
    parseTime
      (UnaryFieldEncoderMachine.unaryFields input.firsts)
      (UnaryFieldEncoderMachine.unaryFields input.seconds)

def scan_evalsInTime (input : Input) :
    EvalsToInTime machine.step
      (scanLeftCfg ⟨encode input, [], [], [], [], [], []⟩)
      (some (reverseOutputCfg
        ⟨[], [], [], [], [], (outputEncoding input).reverse, []⟩))
      (scanTime input) := by
  let firsts := UnaryFieldEncoderMachine.unaryFields input.firsts
  let seconds := UnaryFieldEncoderMachine.unaryFields input.seconds
  let startData : TapeData := ⟨encode input, [], [], [], [], [], []⟩
  let parsedData : TapeData := ⟨[], [], firsts, [], seconds, [], []⟩
  let processedData : TapeData :=
    ⟨[], [], [], [], [], (outputEncoding input).reverse, []⟩
  have parseRun := parsing_evalsInTime firsts seconds
  have parseRun' : EvalsToInTime machine.step (scanLeftCfg startData)
      (some (scanFirstFieldCfg parsedData)) (parseTime firsts seconds) := by
    simpa [startData, parsedData, firsts, seconds, encode,
      SeparatedProductEncoding.encode] using parseRun
  have fieldsRun := fields_evalsInTime input.firsts input.seconds
    [] [] parsedData input.valid
    (by simp [parsedData, firsts])
    (by simp [parsedData, seconds])
  have fieldsRun' : EvalsToInTime machine.step
      (scanFirstFieldCfg parsedData)
      (some (scanFirstFieldCfg processedData))
      (fieldsTime input.firsts input.seconds) := by
    simpa [parsedData, processedData, firsts, seconds,
      outputEncoding] using fieldsRun
  have throughFields := EvalsToInTime.trans machine.step
    (parseTime firsts seconds) (fieldsTime input.firsts input.seconds)
    _ _ _ parseRun' fieldsRun'
  have finish := oneStep (step_scanFirstField_nil processedData rfl)
  have whole := EvalsToInTime.trans machine.step
    (fieldsTime input.firsts input.seconds + parseTime firsts seconds) 1
    _ _ _ throughFields finish
  simpa [startData, processedData, scanTime, firsts, seconds,
    Nat.add_assoc] using whole

end UnaryAlignedAddMachine
end LeanTrominoes
