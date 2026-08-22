/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryBlockRightRotationPositiveBlockExecution
import LeanTrominoes.UnaryBlockRightRotationZeroBlockExecution

/-! # Uniform execution of one unary block right rotation -/

noncomputable section

namespace LeanTrominoes.UnaryBlockRightRotationMachine

open StateTransition Turing

def blockOutputReverse (blockStart : Nat) : Nat → List UnarySymbol
  | 0 => []
  | count + 1 => positiveBlockOutputReverse blockStart count

def blockTime (blockStart : Nat) : Nat → Nat
  | 0 => zeroBlockTime blockStart
  | count + 1 => positiveBlockTime blockStart count

def block_evalsInTime (blockStart groupSize : Nat) (data : TapeData)
    (groupEq : data.group = List.replicate groupSize ())
    (remainingEq : data.groupRemaining = [])
    (startEq : data.start = List.replicate blockStart ())
    (startRestoreEq : data.startRestore = [])
    (positionEq : data.position = [])
    (positionRestoreEq : data.positionRestore = []) :
    EvalsToInTime machine.step (beginGroupCfg data)
      (some (scanSizeFieldCfg
        { data with
          group := []
          groupRemaining := []
          start := []
          startRestore := []
          position := []
          positionRestore := []
          outputReverse :=
            blockOutputReverse blockStart groupSize ++
              data.outputReverse }))
      (blockTime blockStart groupSize) := by
  cases groupSize with
  | zero =>
      simpa [blockTime, blockOutputReverse, remainingEq,
        startRestoreEq, positionRestoreEq] using
        zeroBlock_evalsInTime blockStart data groupEq startEq positionEq
  | succ count =>
      simpa [blockTime, blockOutputReverse] using
        positiveBlock_evalsInTime blockStart count data groupEq
          remainingEq startEq startRestoreEq positionEq positionRestoreEq

end LeanTrominoes.UnaryBlockRightRotationMachine

end
