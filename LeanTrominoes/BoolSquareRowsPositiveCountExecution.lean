/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsCopyExecution
import LeanTrominoes.BoolSquareRowsRoundsExecution

/-! # Setup and counting for positive Boolean squares -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace BoolSquareRowsMachine

@[simp] theorem workTokens_eq_replicate (bits : List Bool) :
    workTokens bits = List.replicate bits.length () := by
  simp [workTokens]

def positiveCountTime (bits : List Bool) (additionalRounds : Nat) : Nat :=
  rootRoundsCost 0 additionalRounds + (bits.length + 2)

/-- Copying a Boolean square of side `additionalRounds + 1` and running the
odd-interval counter produces that side length on the root stack. -/
def positiveCount_evalsInTime (bits : List Bool) (additionalRounds : Nat)
    (lengthEq : bits.length = (additionalRounds + 1) ^ 2) :
    EvalsToInTime (TM2.step program)
      (copyInputCfg
        ⟨bits, [], [], [], [], [], [], [], [], [], []⟩)
      (some (clearOddCfg
        ⟨[], bits.reverse, [], [],
          List.replicate (2 * additionalRounds + 1) (),
          List.replicate (additionalRounds + 1) (),
          [], [], [], [], []⟩))
      (positiveCountTime bits additionalRounds) := by
  let initial : TapeData :=
    ⟨bits, [], [], [], [], [], [], [], [], [], []⟩
  let copied : TapeData :=
    ⟨[], bits.reverse, workTokens bits, [], [], [], [], [], [], [], []⟩
  let ready : TapeData :=
    ⟨[], bits.reverse, workTokens bits, [()], [], [], [], [], [], [], []⟩
  have copiedRun := copyInput_evalsInTime bits initial rfl
  have initialized := oneStep (step_initOdd copied)
  have throughInit := EvalsToInTime.trans (TM2.step program)
    (bits.length + 1) 1
    (copyInputCfg initial) (initOddCfg copied)
    (some (consumeWorkCfg ready))
    (by simpa [initial, copied] using copiedRun)
    (by simpa only [ready, copied] using initialized)
  have counted := rootRounds_evalsInTime 0 additionalRounds ready
    (by simp [ready, lengthEq, remainingWork_zero_left])
    (by simp [ready]) (by simp [ready])
  have whole := EvalsToInTime.trans (TM2.step program)
    (1 + (bits.length + 1)) (rootRoundsCost 0 additionalRounds)
    (copyInputCfg initial) (consumeWorkCfg ready)
    (some (clearOddCfg
      { ready with
        work := []
        odd := []
        oddRestore := List.replicate (2 * additionalRounds + 1) ()
        root := List.replicate (additionalRounds + 1) () }))
    (by simpa using throughInit) (by simpa [ready] using counted)
  convert whole using 1
  simp [positiveCountTime]
  omega

end BoolSquareRowsMachine
end LeanTrominoes
