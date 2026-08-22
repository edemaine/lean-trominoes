/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupBitExecution

/-! # Executing one row of a last-true unary lookup -/

noncomputable section

namespace LeanTrominoes
namespace LastTrueUnaryValueLookupMachine

open StateTransition Turing

private def oneStep {before after : machine.Cfg}
    (step : machine.step before = some after) :
    EvalsToInTime machine.step before (some after) 1 where
  steps := 1
  evals_in_steps := by
    simp only [Function.iterate_one]
    exact step
  steps_le_m := Nat.le_refl 1

/-- Exact cost of opening, evaluating, emitting, and restoring one row. -/
def rowTime (row : List Bool) (values : List Nat) : Nat :=
  1 + bitsTime 0 row values +
    (2 * lookup row values + 1) + 1 +
      (2 * (UnaryFieldEncoderMachine.unaryFields values).length + 1)

def row_evalsInTime (row : List Bool) (values : List Nat)
    (rowsTail : List RowSymbol) (data : TapeData)
    (valid : RowValid row values)
    (rowsEq : data.rows =
      DelimitedBinaryWords.wordTokens row ++ rowsTail)
    (valuesEq : data.values =
      UnaryFieldEncoderMachine.unaryFields values)
    (restoreEq : data.valuesRestore = [])
    (candidateEq : data.candidate = []) :
    EvalsToInTime machine.step (scanRowsCfg data)
      (some (scanRowsCfg
        { data with
          rows := rowsTail
          values := UnaryFieldEncoderMachine.unaryFields values
          valuesRestore := []
          candidate := []
          outputReverse :=
            (UnaryFieldEncoderMachine.unaryField
              (lookup row values)).reverse ++ data.outputReverse }))
      (rowTime row values) := by
  let rowBody : List RowSymbol :=
    row.map .bit ++ .wordEnd :: rowsTail
  let afterStart : TapeData :=
    { data with rows := rowBody }
  let afterBits : TapeData :=
    { data with
      rows := rowsTail
      values := []
      valuesRestore :=
        (UnaryFieldEncoderMachine.unaryFields values).reverse
      candidate := List.replicate (lookup row values) () }
  let afterDrain : TapeData :=
    { afterBits with
      candidate := []
      outputReverse :=
        List.replicate (lookup row values) .unit ++
          data.outputReverse }
  let afterDelimiter : TapeData :=
    { afterDrain with
      outputReverse := .delimiter :: afterDrain.outputReverse }
  have rowsHead : data.rows = .wordStart :: rowBody := by
    simpa [DelimitedBinaryWords.wordTokens, rowBody,
      List.append_assoc] using rowsEq
  have started := oneStep
    (step_scanRows_start data rowBody rowsHead)
  have started' : EvalsToInTime machine.step (scanRowsCfg data)
      (some (nextBitCfg afterStart)) 1 := by
    simpa [afterStart] using started
  have scanned := bits_evalsInTime 0 row values rowsTail afterStart valid
    (by simp [afterStart, rowBody])
    (by simpa [afterStart] using valuesEq)
    (by simpa [afterStart] using candidateEq)
  have scanned' : EvalsToInTime machine.step (nextBitCfg afterStart)
      (some (drainCandidateCfg afterBits))
      (bitsTime 0 row values) := by
    simpa [afterStart, afterBits, lookup, restoreEq] using scanned
  have drained := drainCandidate_evalsInTime
    (List.replicate (lookup row values) ()) afterBits rfl
  have drained' : EvalsToInTime machine.step (drainCandidateCfg afterBits)
      (some (emitDelimiterCfg afterDrain))
      (2 * lookup row values + 1) := by
    simpa [afterDrain] using drained
  have delimited := oneStep (step_emitDelimiter afterDrain)
  have delimited' : EvalsToInTime machine.step (emitDelimiterCfg afterDrain)
      (some (restoreValuesCfg afterDelimiter)) 1 := by
    simpa [afterDelimiter] using delimited
  have restored := restoreValues_evalsInTime
    (UnaryFieldEncoderMachine.unaryFields values).reverse
    afterDelimiter rfl
  have throughBits := EvalsToInTime.trans machine.step
    1 (bitsTime 0 row values) _ _ _ started' scanned'
  have throughDrain := EvalsToInTime.trans machine.step
    (bitsTime 0 row values + 1) (2 * lookup row values + 1)
    _ _ _ throughBits drained'
  have throughDelimiter := EvalsToInTime.trans machine.step
    (2 * lookup row values + 1 + (bitsTime 0 row values + 1)) 1
    _ _ _ throughDrain delimited'
  have whole := EvalsToInTime.trans machine.step
    (1 + (2 * lookup row values + 1 +
      (bitsTime 0 row values + 1)))
    (2 * (UnaryFieldEncoderMachine.unaryFields values).reverse.length + 1)
    _ _ _ throughDelimiter restored
  convert whole using 1
  · simp [afterDelimiter, afterDrain, afterBits,
      UnaryFieldEncoderMachine.unaryField,
      List.reverse_append]
  · simp [rowTime]
    omega

end LastTrueUnaryValueLookupMachine
end LeanTrominoes
