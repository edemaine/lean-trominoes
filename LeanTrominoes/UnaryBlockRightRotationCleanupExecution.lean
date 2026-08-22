/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryBlockRightRotationExecutionSupport
import LeanTrominoes.UnaryBlockRightRotationRemainingSteps

/-! # Clearing per-block counters after unary block right rotation -/

noncomputable section

namespace LeanTrominoes.UnaryBlockRightRotationMachine

open StateTransition Turing

def clearStart_evalsInTime (count : Nat) (data : TapeData)
    (startEq : data.start = List.replicate count ()) :
    EvalsToInTime machine.step (clearStartCfg data)
      (some (clearPositionCfg { data with start := [] }))
      (count + 1) := by
  induction count generalizing data with
  | zero =>
      have step := step_clearStart_nil data (by simpa using startEq)
      simpa using oneStep step
  | succ count induction =>
      have startHead : data.start = () :: List.replicate count () := by
        simpa [List.replicate_succ] using startEq
      let first := oneStep
        (step_clearStart_cons data (List.replicate count ()) startHead)
      let nextData : TapeData :=
        { data with start := List.replicate count () }
      let rest := induction nextData rfl
      let whole := EvalsToInTime.trans machine.step
        1 (count + 1) _ _ _ first rest
      simpa [whole, nextData, Nat.add_assoc] using whole

def clearPosition_evalsInTime (count : Nat) (data : TapeData)
    (positionEq : data.position = List.replicate count ()) :
    EvalsToInTime machine.step (clearPositionCfg data)
      (some (scanSizeFieldCfg { data with position := [] }))
      (count + 1) := by
  induction count generalizing data with
  | zero =>
      have step := step_clearPosition_nil data (by simpa using positionEq)
      simpa using oneStep step
  | succ count induction =>
      have positionHead : data.position =
          () :: List.replicate count () := by
        simpa [List.replicate_succ] using positionEq
      let first := oneStep
        (step_clearPosition_cons data
          (List.replicate count ()) positionHead)
      let nextData : TapeData :=
        { data with position := List.replicate count () }
      let rest := induction nextData rfl
      let whole := EvalsToInTime.trans machine.step
        1 (count + 1) _ _ _ first rest
      simpa [whole, nextData, Nat.add_assoc] using whole

end LeanTrominoes.UnaryBlockRightRotationMachine

end
