/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryRotatedRanksListExecution
import LeanTrominoes.UnaryRotatedRanksParsing

/-! # Complete parsing and scanning for unary rotated ranks -/

noncomputable section

namespace LeanTrominoes
namespace UnaryRotatedRanksMachine

open StateTransition Turing

private def oneStep {before after : machine.Cfg}
    (step : machine.step before = some after) :
    EvalsToInTime machine.step before (some after) 1 where
  steps := 1
  evals_in_steps := by
    simp only [Function.iterate_one]
    exact step
  steps_le_m := Nat.le_refl 1

def scanTime (input : Input) : Nat :=
  1 + fieldsTime input.ranks input.sizes +
    parseTime
      (UnaryFieldEncoderMachine.unaryFields input.ranks)
      (UnaryFieldEncoderMachine.unaryFields input.sizes)

def scan_evalsInTime (input : Input) :
    EvalsToInTime machine.step
      (scanLeftCfg ⟨encode input, [], [], [], [], [], []⟩)
      (some (reverseOutputCfg
        ⟨[], [], [], [], [], (outputEncoding input).reverse, []⟩))
      (scanTime input) := by
  let ranks := UnaryFieldEncoderMachine.unaryFields input.ranks
  let sizes := UnaryFieldEncoderMachine.unaryFields input.sizes
  let startData : TapeData := ⟨encode input, [], [], [], [], [], []⟩
  let parsedData : TapeData := ⟨[], [], ranks, [], sizes, [], []⟩
  let processedData : TapeData :=
    ⟨[], [], [], [], [], (outputEncoding input).reverse, []⟩
  have parseRun := parsing_evalsInTime ranks sizes
  have parseRun' : EvalsToInTime machine.step (scanLeftCfg startData)
      (some (scanRankCfg parsedData)) (parseTime ranks sizes) := by
    simpa [startData, parsedData, ranks, sizes, encode,
      SeparatedProductEncoding.encode] using parseRun
  have fieldsRun := fields_evalsInTime input.ranks input.sizes
    [] [] parsedData input.valid
    (by simp [parsedData, ranks])
    (by simp [parsedData, sizes])
  have fieldsRun' : EvalsToInTime machine.step (scanRankCfg parsedData)
      (some (scanRankCfg processedData))
      (fieldsTime input.ranks input.sizes) := by
    simpa [parsedData, processedData, ranks, sizes, outputEncoding] using
      fieldsRun
  have throughFields := EvalsToInTime.trans machine.step
    (parseTime ranks sizes) (fieldsTime input.ranks input.sizes)
    _ _ _ parseRun' fieldsRun'
  have finish := oneStep (step_scanRank_nil processedData rfl)
  have whole := EvalsToInTime.trans machine.step
    (fieldsTime input.ranks input.sizes + parseTime ranks sizes) 1
    _ _ _ throughFields finish
  simpa [startData, processedData, scanTime, ranks, sizes,
    Nat.add_assoc] using whole

end UnaryRotatedRanksMachine
end LeanTrominoes
