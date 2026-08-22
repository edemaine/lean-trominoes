/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryRotatedRanksInput
import LeanTrominoes.UnaryRotatedRanksLocalExecution

/-! # Complete field execution for unary rotated ranks -/

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

def field_evalsInTime (rank size : Nat)
    (ranksTail sizesTail : List UnarySymbol) (data : TapeData)
    (rankLtSize : rank < size)
    (ranksEq : data.ranks =
      UnaryFieldEncoderMachine.unaryField rank ++ ranksTail)
    (sizesEq : data.sizes =
      UnaryFieldEncoderMachine.unaryField size ++ sizesTail) :
    EvalsToInTime machine.step (scanRankCfg data)
      (some (scanRankCfg
        { data with
          ranks := ranksTail
          sizes := sizesTail
          outputReverse :=
            (UnaryFieldEncoderMachine.unaryField
              (rotatedRank rank size)).reverse ++ data.outputReverse }))
      (fieldTime rank size) := by
  cases rank with
  | zero =>
      cases size with
      | zero => omega
      | succ units =>
          let afterRank : TapeData := { data with ranks := ranksTail }
          let afterFirstSize : TapeData :=
            { afterRank with
              sizes := UnaryFieldEncoderMachine.unaryField units ++
                sizesTail }
          let afterUnits : TapeData :=
            { afterFirstSize with
              sizes := sizesTail
              outputReverse :=
                List.replicate units .unit ++ data.outputReverse }
          have rankHead : data.ranks = .delimiter :: ranksTail := by
            simpa [UnaryFieldEncoderMachine.unaryField] using ranksEq
          have openedRank := oneStep
            (step_scanRank_delimiter data ranksTail rankHead)
          have openedRank' : EvalsToInTime machine.step (scanRankCfg data)
              (some (zeroRankFirstSizeCfg afterRank)) 1 := by
            simpa [afterRank] using openedRank
          have sizeHead : afterRank.sizes = .unit ::
              (UnaryFieldEncoderMachine.unaryField units ++ sizesTail) := by
            simpa [afterRank, UnaryFieldEncoderMachine.unaryField,
              List.replicate_succ] using sizesEq
          have openedSize := oneStep
            (step_zeroRankFirstSize_unit afterRank
              (UnaryFieldEncoderMachine.unaryField units ++ sizesTail)
              sizeHead)
          have openedSize' : EvalsToInTime machine.step
              (zeroRankFirstSizeCfg afterRank)
              (some (zeroRankRestSizeCfg afterFirstSize)) 1 := by
            simpa [afterFirstSize] using openedSize
          have copied := copyZero_evalsInTime units sizesTail
            afterFirstSize
            (by simp [afterFirstSize, UnaryFieldEncoderMachine.unaryField])
          have copied' : EvalsToInTime machine.step
              (zeroRankRestSizeCfg afterFirstSize)
              (some (emitDelimiterCfg afterUnits)) (2 * units + 1) := by
            simpa [afterUnits] using copied
          have delimited := oneStep (step_emitDelimiter afterUnits)
          have throughOpen := EvalsToInTime.trans machine.step
            1 1 _ _ _ openedRank' openedSize'
          have throughUnits := EvalsToInTime.trans machine.step
            2 (2 * units + 1) _ _ _ throughOpen copied'
          have whole := EvalsToInTime.trans machine.step
            (2 * units + 1 + 2) 1 _ _ _ throughUnits delimited
          convert whole using 1
          · simp [afterUnits, afterFirstSize, afterRank,
              rotatedRank, UnaryFieldEncoderMachine.unaryField,
              List.reverse_append]
          · simp [fieldTime]
            omega
  | succ units =>
      let afterRank : TapeData :=
        { data with
          ranks := UnaryFieldEncoderMachine.unaryField units ++ ranksTail }
      let afterUnits : TapeData :=
        { afterRank with
          ranks := ranksTail
          outputReverse :=
            List.replicate units .unit ++ data.outputReverse }
      let afterSize : TapeData := { afterUnits with sizes := sizesTail }
      have rankHead : data.ranks = .unit ::
          (UnaryFieldEncoderMachine.unaryField units ++ ranksTail) := by
        simpa [UnaryFieldEncoderMachine.unaryField,
          List.replicate_succ] using ranksEq
      have opened := oneStep
        (step_scanRank_unit data
          (UnaryFieldEncoderMachine.unaryField units ++ ranksTail) rankHead)
      have opened' : EvalsToInTime machine.step (scanRankCfg data)
          (some (positiveRankRestCfg afterRank)) 1 := by
        simpa [afterRank] using opened
      have copied := copyPositive_evalsInTime units ranksTail afterRank
        (by simp [afterRank, UnaryFieldEncoderMachine.unaryField])
      have copied' : EvalsToInTime machine.step
          (positiveRankRestCfg afterRank)
          (some (drainSizeCfg afterUnits)) (2 * units + 1) := by
        simpa [afterUnits] using copied
      have drained := drainSize_evalsInTime size sizesTail afterUnits
        (by simpa [afterUnits, afterRank] using sizesEq)
      have drained' : EvalsToInTime machine.step (drainSizeCfg afterUnits)
          (some (emitDelimiterCfg afterSize)) (size + 1) := by
        simpa [afterSize] using drained
      have delimited := oneStep (step_emitDelimiter afterSize)
      have throughUnits := EvalsToInTime.trans machine.step
        1 (2 * units + 1) _ _ _ opened' copied'
      have throughSize := EvalsToInTime.trans machine.step
        (2 * units + 1 + 1) (size + 1) _ _ _ throughUnits drained'
      have whole := EvalsToInTime.trans machine.step
        (size + 1 + (2 * units + 1 + 1)) 1
        _ _ _ throughSize delimited
      convert whole using 1
      · simp [afterSize, afterUnits, afterRank,
          rotatedRank, UnaryFieldEncoderMachine.unaryField,
          List.reverse_append]
      · simp [fieldTime]
        omega

end UnaryRotatedRanksMachine
end LeanTrominoes
