/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryBlockRightRotationExecutionSupport
import LeanTrominoes.UnaryBlockRightRotationRemainingSteps

/-! # Copying and restoring positions for remaining block values -/

noncomputable section

namespace LeanTrominoes.UnaryBlockRightRotationMachine

open StateTransition Turing

def copyPosition_evalsInTime (count : Nat) (data : TapeData)
    (positionEq : data.position = List.replicate count ()) :
    EvalsToInTime machine.step (copyPositionCfg data)
      (some (restorePositionCfg
        { data with
          position := []
          positionRestore :=
            List.replicate count () ++ data.positionRestore
          outputReverse :=
            List.replicate count .unit ++ data.outputReverse }))
      (count + 1) := by
  induction count generalizing data with
  | zero =>
      have step := step_copyPosition_nil data (by simpa using positionEq)
      simpa using oneStep step
  | succ count induction =>
      have positionHead : data.position =
          () :: List.replicate count () := by
        simpa [List.replicate_succ] using positionEq
      let first := oneStep
        (step_copyPosition_cons data (List.replicate count ()) positionHead)
      let nextData : TapeData :=
        { data with
          position := List.replicate count ()
          positionRestore := () :: data.positionRestore
          outputReverse := .unit :: data.outputReverse }
      let rest := induction nextData rfl
      let whole := EvalsToInTime.trans machine.step
        1 (count + 1) _ _ _ first rest
      simpa [whole, nextData, List.replicate_succ,
        replicate_unit_cons_comm, replicate_value_cons_comm,
        List.append_assoc, Nat.add_assoc] using whole

def restorePosition_evalsInTime (count : Nat) (data : TapeData)
    (restoreEq : data.positionRestore = List.replicate count ()) :
    EvalsToInTime machine.step (restorePositionCfg data)
      (some (emitRemainingDelimiterCfg
        { data with
          positionRestore := []
          position := List.replicate count () ++ data.position }))
      (count + 1) := by
  induction count generalizing data with
  | zero =>
      have step := step_restorePosition_nil data (by simpa using restoreEq)
      simpa using oneStep step
  | succ count induction =>
      have restoreHead : data.positionRestore =
          () :: List.replicate count () := by
        simpa [List.replicate_succ] using restoreEq
      let first := oneStep
        (step_restorePosition_cons data
          (List.replicate count ()) restoreHead)
      let nextData : TapeData :=
        { data with
          positionRestore := List.replicate count ()
          position := () :: data.position }
      let rest := induction nextData rfl
      let whole := EvalsToInTime.trans machine.step
        1 (count + 1) _ _ _ first rest
      simpa [whole, nextData, List.replicate_succ,
        replicate_value_cons_comm, List.append_assoc,
        Nat.add_assoc] using whole

end LeanTrominoes.UnaryBlockRightRotationMachine

end
