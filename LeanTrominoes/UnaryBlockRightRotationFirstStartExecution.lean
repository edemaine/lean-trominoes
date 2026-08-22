/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryBlockRightRotationExecutionSupport
import LeanTrominoes.UnaryBlockRightRotationFirstOutputSteps

/-! # Copying and restoring the first block start -/

noncomputable section

namespace LeanTrominoes.UnaryBlockRightRotationMachine

open StateTransition Turing

def copyFirstStart_evalsInTime (count : Nat) (data : TapeData)
    (startEq : data.start = List.replicate count ()) :
    EvalsToInTime machine.step (copyFirstStartCfg data)
      (some (restoreFirstStartCfg
        { data with
          start := []
          startRestore := List.replicate count () ++ data.startRestore
          outputReverse :=
            List.replicate count .unit ++ data.outputReverse }))
      (count + 1) := by
  induction count generalizing data with
  | zero =>
      have step := step_copyFirstStart_nil data (by simpa using startEq)
      simpa using oneStep step
  | succ count induction =>
      have startHead : data.start = () :: List.replicate count () := by
        simpa [List.replicate_succ] using startEq
      let first := oneStep
        (step_copyFirstStart_cons data (List.replicate count ()) startHead)
      let nextData : TapeData :=
        { data with
          start := List.replicate count ()
          startRestore := () :: data.startRestore
          outputReverse := .unit :: data.outputReverse }
      let rest := induction nextData rfl
      let whole := EvalsToInTime.trans machine.step
        1 (count + 1) _ _ _ first rest
      simpa [whole, nextData, List.replicate_succ,
        replicate_unit_cons_comm, replicate_value_cons_comm,
        List.append_assoc, Nat.add_assoc] using whole

def restoreFirstStart_evalsInTime (count : Nat) (data : TapeData)
    (restoreEq : data.startRestore = List.replicate count ()) :
    EvalsToInTime machine.step (restoreFirstStartCfg data)
      (some (copyFirstGroupCfg
        { data with
          startRestore := []
          start := List.replicate count () ++ data.start }))
      (count + 1) := by
  induction count generalizing data with
  | zero =>
      have step := step_restoreFirstStart_nil data (by simpa using restoreEq)
      simpa using oneStep step
  | succ count induction =>
      have restoreHead : data.startRestore =
          () :: List.replicate count () := by
        simpa [List.replicate_succ] using restoreEq
      let first := oneStep
        (step_restoreFirstStart_cons data
          (List.replicate count ()) restoreHead)
      let nextData : TapeData :=
        { data with
          startRestore := List.replicate count ()
          start := () :: data.start }
      let rest := induction nextData rfl
      let whole := EvalsToInTime.trans machine.step
        1 (count + 1) _ _ _ first rest
      simpa [whole, nextData, List.replicate_succ,
        replicate_value_cons_comm, List.append_assoc,
        Nat.add_assoc] using whole

end LeanTrominoes.UnaryBlockRightRotationMachine

end
