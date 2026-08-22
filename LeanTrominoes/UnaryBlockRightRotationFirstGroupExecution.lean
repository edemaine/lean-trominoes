/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryBlockRightRotationExecutionSupport
import LeanTrominoes.UnaryBlockRightRotationFirstOutputSteps

/-! # Copying the first block's remaining units -/

noncomputable section

namespace LeanTrominoes.UnaryBlockRightRotationMachine

open StateTransition Turing

def copyFirstGroup_evalsInTime (count : Nat) (data : TapeData)
    (groupEq : data.group = List.replicate count ()) :
    EvalsToInTime machine.step (copyFirstGroupCfg data)
      (some (emitFirstDelimiterCfg
        { data with
          group := []
          groupRemaining :=
            List.replicate count () ++ data.groupRemaining
          outputReverse :=
            List.replicate count .unit ++ data.outputReverse }))
      (count + 1) := by
  induction count generalizing data with
  | zero =>
      have step := step_copyFirstGroup_nil data (by simpa using groupEq)
      simpa using oneStep step
  | succ count induction =>
      have groupHead : data.group = () :: List.replicate count () := by
        simpa [List.replicate_succ] using groupEq
      let first := oneStep
        (step_copyFirstGroup_cons data (List.replicate count ()) groupHead)
      let nextData : TapeData :=
        { data with
          group := List.replicate count ()
          groupRemaining := () :: data.groupRemaining
          outputReverse := .unit :: data.outputReverse }
      let rest := induction nextData rfl
      let whole := EvalsToInTime.trans machine.step
        1 (count + 1) _ _ _ first rest
      simpa [whole, nextData, List.replicate_succ,
        replicate_unit_cons_comm, replicate_value_cons_comm,
        List.append_assoc, Nat.add_assoc] using whole

end LeanTrominoes.UnaryBlockRightRotationMachine

end
